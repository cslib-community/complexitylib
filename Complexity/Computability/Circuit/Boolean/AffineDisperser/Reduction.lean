/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Operations

/-!
# Reductions and their accounting

Every reduction of the gate elimination of [Mishra and Santhanam, Section 4][MishraSanthanam2026]
restricts some parameters and then deletes some gates and equations. A *reduction*
(`State.Reduction f S S' F D T`) from `S` to `S'` restricts the parameters of `F`, each to a
constant or to a literal of a remaining parameter with at least its children, drops the pairs
meeting `F`, and then deletes the constraints of the list `D`. Only the deletions of the
constraints of `T` may reroute a constraint to a parameter; the others reroute to constants or to
non-parameters. Reductions compose (`State.Reduction.trans`), and are built from restrictions
(`State.Valid.reduction_restrict`, `State.Valid.reduction_fixConst`) and deletions
(`State.Valid.reduction_deleteGate`, `State.Valid.reduction_deleteEqn`,
`State.Valid.exists_reduction_deleteAll`).

The accounting is done once for all reductions:

* `Δm = -|F|`, `Δs = -|D|` and `Δq = -k`, where `k` is the number of pairs meeting `F`
  (`State.Reduction.m_add`, `State.Reduction.s_add`, `State.Reduction.q_add`);
* the unpaired parameters of `S'` are those of `S` outside `F`, together with the partners of
  members of `F` (`State.Reduction.mem_unpaired_iff`);
* a parameter that no deletion of `T` reroutes to keeps at most its children outside `D`
  (`State.Reduction.wt_le_weight`), and an unpaired parameter rerouted to only by deletions of
  constraints with another parameter as a parent does not gain weight in an *exclusive* state
  (`State.Reduction.wt_le_of_exclusive`);
* the potential: `W' + 2 |D| + 3 k + ∑_{x ∈ F} wt(x) ≤ W` plus the pointwise gains
  (`State.Reduction.W_le`), and a reduction restricting at most two parameters with
  `W' + 14 |F| ≤ W + 14 k` is a step of gate elimination (`State.Reduction.step`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.Reduction`: reductions.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Deletable`: constraints deletable by (D1) or
  (D3).
* `Cslib.Circuits.Boolean.AffineDisperser.State.Exclusive`: no constraint has an unpaired
  isolated parameter and another parameter as parents.
* `Cslib.Circuits.Boolean.AffineDisperser.State.fixConst`: fixing a parameter to a constant.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Reduction.W_le`: the potential of a reduction.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Reduction.step`: reductions as steps of gate
  elimination.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_reduction_deleteAll`: deleting
  deletable constraints.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Exclusive states -/

/-- No constraint has both an unpaired isolated parameter and another parameter as parents. -/
def Exclusive (S : State n) : Prop :=
  ∀ z ∈ S.unpaired, S.deg z = 1 → ∀ N ∈ S.children z, ∀ z' ∈ S.params, z' ≠ z →
    N ∉ S.children z'

/-- In an exclusive state, an unpaired parameter sharing a child with another parameter has
degree at least two. -/
theorem Exclusive.two_le_deg {S : State n} (h : S.Exclusive) {u x : ℕ} {N : ℕ ⊕ ℕ}
    (hu : u ∈ S.unpaired) (hNu : N ∈ S.children u) (hx : x ∈ S.params) (hxu : x ≠ u)
    (hNx : N ∈ S.children x) : 2 ≤ S.deg u := by
  have : 1 ≤ S.deg u := Finset.card_pos.2 ⟨N, hNu⟩
  by_contra hlt
  exact h u hu (by omega) N hNu x hx hxu hNx

/-! ### Deletable constraints -/

/-- A deletable constraint: a gate with a constant argument or two equal arguments, or an
equation with at most two terms. -/
def Deletable (S : State n) : ℕ ⊕ ℕ → Prop
  | .inl J => J ∈ S.gates ∧ (S.gate J).Degenerate
  | .inr e => e ∈ S.eqns ∧ (S.eqn e).terms.card ≤ 2

/-- The children of a parameter fixed to a constant are deletable. -/
theorem deletable_fixConst_child {S : State n} (hS : S.Valid f) {p : ℕ} (P : Finset (ℕ × ℕ))
    (b : Bool) {N : ℕ ⊕ ℕ} (hN : N ∈ S.children p) :
    (S.restrict p (Lit.const b) P).Deletable N := by
  rcases N with J | e
  · obtain ⟨hJ, hr⟩ := (SemiCircuit.inl_mem_children _).1 hN
    refine ⟨hJ, ?_⟩
    change ((S.gate J).subst p (Lit.const b)).Degenerate
    unfold Gate.Degenerate
    change (∃ c, (S.gate J).left.substArg p (Arg.const b) = .const c) ∨
      (∃ c, (S.gate J).right.substArg p (Arg.const b) = .const c) ∨ _
    rcases hr with hr | hr
    · exact Or.inl ⟨b, by rw [hr]; simp [Arg.substArg]⟩
    · exact Or.inr (Or.inl ⟨b, by rw [hr]; simp [Arg.substArg]⟩)
  · obtain ⟨he, hpe⟩ := (SemiCircuit.inr_mem_children _).1 hN
    refine ⟨he, ?_⟩
    change ((S.eqn e).subst p (Lit.const b)).terms.card ≤ 2
    have h3 := hS.wf.card_terms_le e he
    have : ((S.eqn e).subst p (Lit.const b)).terms = (S.eqn e).terms.erase p := by
      simp [Equation.subst, hpe, Lit.const]
    rw [this, Finset.card_erase_of_mem hpe]
    omega

/-- After deleting the gate `J` rerouted to a constant, the gates reading `J` are deletable. -/
theorem deletable_deleteGate_child {S : State n} {J K : ℕ} (c : Bool) (hK : K ∈ S.gates)
    (hKJ : K ≠ J) (hr : (S.gate K).Reads J) :
    (S.deleteGate J (Lit.const c)).Deletable (.inl K) := by
  refine ⟨Finset.mem_erase.2 ⟨hKJ, hK⟩, ?_⟩
  change ((S.gate K).subst J (Lit.const c)).Degenerate
  unfold Gate.Degenerate
  change (∃ b, (S.gate K).left.substArg J (Arg.const c) = .const b) ∨
    (∃ b, (S.gate K).right.substArg J (Arg.const c) = .const b) ∨ _
  rcases hr with hr | hr
  · exact Or.inl ⟨c, by rw [hr]; simp [Arg.substArg]⟩
  · exact Or.inr (Or.inl ⟨c, by rw [hr]; simp [Arg.substArg]⟩)

/-! ### Reductions -/

/-- A reduction from `S` to `S'`: the parameters of `F` are restricted, each to a constant or to
a literal of a remaining parameter having at least its children, the pairs meeting `F` are
dropped, and the constraints of `D` are deleted. The children of a remaining parameter lose the
deleted constraints and gain none, unless a deletion of a constraint of `T` that was one of its
children reroutes to it; and the other constraints stay deletable. -/
structure Reduction (f : BooleanFunction n) (S S' : State n) (F : Finset ℕ)
    (D T : List (ℕ ⊕ ℕ)) : Prop where
  /-- The new state is valid. -/
  valid : S'.Valid f
  /-- The restricted names are parameters. -/
  subset : F ⊆ S.params
  /-- The restricted parameters are removed. -/
  params : S'.params = S.params \ F
  /-- The pairs meeting the restricted parameters are dropped. -/
  pairs : S'.pairs = S.pairs.filter fun pr => ¬ (pr.1 ∈ F ∨ pr.2 ∈ F)
  /-- The deleted constraints are removed. -/
  size : S'.size + D.length = S.size
  /-- A remaining parameter gains no child, unless a deletion of `T` reroutes to it. -/
  children : ∀ u ∈ S'.params,
    S'.children u ⊆ S.children u \ D.toFinset ∨ ∃ N ∈ T, N ∈ S.children u
  /-- The other constraints stay deletable. -/
  deletable : ∀ N, N ∉ D → S.Deletable N → S'.Deletable N

namespace Reduction

variable {S S' : State n} {F : Finset ℕ} {D T : List (ℕ ⊕ ℕ)}

/-- The empty reduction from a valid state `S` to itself. -/
theorem refl (hS : S.Valid f) : Reduction f S S ∅ [] [] where
  valid := hS
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := rfl
  children _ _ := Or.inl (by simp)
  deletable _ _ h := h

/-- Reductions compose. -/
theorem trans {S₁ S₂ : State n} {F₁ F₂ : Finset ℕ} {D₁ D₂ T₁ T₂ : List (ℕ ⊕ ℕ)}
    (h₁ : Reduction f S S₁ F₁ D₁ T₁) (h₂ : Reduction f S₁ S₂ F₂ D₂ T₂) :
    Reduction f S S₂ (F₁ ∪ F₂) (D₁ ++ D₂) (T₁ ++ T₂) where
  valid := h₂.valid
  subset := Finset.union_subset h₁.subset ((h₂.subset.trans h₁.params.le).trans sdiff_subset)
  params := by
    rw [h₂.params, h₁.params]
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  pairs := by
    rw [h₂.pairs, h₁.pairs, Finset.filter_filter]
    exact Finset.filter_congr fun pr _ => by simp only [Finset.mem_union]; tauto
  size := by rw [List.length_append, ← h₁.size, ← h₂.size]; omega
  children u hu := by
    have hu₁ : u ∈ S₁.params := (h₂.params.le hu |> Finset.mem_sdiff.1).1
    rcases h₂.children u hu with h₂' | ⟨N, hN, hNu⟩ <;> rcases h₁.children u hu₁ with h₁' | h₁'
    · refine Or.inl fun N hN => ?_
      have h₂N := Finset.mem_sdiff.1 (h₂' hN)
      have h₁N := Finset.mem_sdiff.1 (h₁' h₂N.1)
      simp only [Finset.mem_sdiff, List.toFinset_append, Finset.mem_union, not_or]
      exact ⟨h₁N.1, h₁N.2, h₂N.2⟩
    · obtain ⟨N, hN, hNu⟩ := h₁'
      exact Or.inr ⟨N, List.mem_append_left _ hN, hNu⟩
    · exact Or.inr ⟨N, List.mem_append_right _ hN, (Finset.mem_sdiff.1 (h₁' hNu)).1⟩
    · obtain ⟨N, hN, hNu⟩ := h₁'
      exact Or.inr ⟨N, List.mem_append_left _ hN, hNu⟩
  deletable N hN h := by
    rw [List.mem_append, not_or] at hN
    exact h₂.deletable N hN.2 (h₁.deletable N hN.1 h)

/-- A reduction followed by a reduction restricting nothing. -/
theorem trans_delete {S₁ S₂ : State n} {D₂ T₂ : List (ℕ ⊕ ℕ)} (h₁ : Reduction f S S₁ F D T)
    (h₂ : Reduction f S₁ S₂ ∅ D₂ T₂) : Reduction f S S₂ F (D ++ D₂) (T ++ T₂) := by
  have h := h₁.trans h₂
  rwa [Finset.union_empty] at h

/-- A reduction may record more deletions as possibly rerouting to parameters. -/
theorem mono (h : Reduction f S S' F D T) {T' : List (ℕ ⊕ ℕ)} (hT : ∀ N ∈ T, N ∈ T') :
    Reduction f S S' F D T' :=
  { h with
    children := fun u hu => (h.children u hu).imp_right fun ⟨N, hN, hNu⟩ => ⟨N, hT N hN, hNu⟩ }

/-! ### Accounting -/

/-- A reduction restricting `F` decreases the number of parameters `m` by `|F|`. -/
theorem m_add (h : Reduction f S S' F D T) : S'.m + F.card = S.m := by
  unfold m
  rw [h.params, Finset.card_sdiff_of_subset h.subset]
  have := Finset.card_le_card h.subset
  omega

/-- A reduction deleting `D` decreases the size `s` by `|D|`. -/
theorem s_add (h : Reduction f S S' F D T) : S'.s + D.length = S.s :=
  h.size

/-- A reduction restricting `F` decreases the number of pairs `q` by the number of pairs meeting
`F`. -/
theorem q_add (h : Reduction f S S' F D T) : S'.q + (S.pairsMeeting F).card = S.q := by
  unfold q pairsMeeting
  rw [h.pairs, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- Under a reduction restricting `F`, `S'.a + |F| = S.a + (S.pairsMeeting F).card`. -/
theorem a_add (h : Reduction f S S' F D T) (hS : S.Valid f) :
    S'.a + F.card = S.a + (S.pairsMeeting F).card := by
  have hm := h.m_add
  have hq := h.q_add
  have hk := hS.card_pairsMeeting_le F
  have hqm := h.valid.q_le_m
  unfold a
  omega

/-- The unpaired parameters after a reduction: the unpaired parameters outside `F` and the
partners of members of `F`. -/
theorem mem_unpaired_iff (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ} :
    u ∈ S'.unpaired ↔ u ∈ S.params ∧ u ∉ F ∧ (¬ S.Paired u ∨ ∃ x ∈ F, S.IsPartner x u) := by
  rw [mem_unpaired, h.params, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hu, huF⟩, hun⟩
    refine ⟨hu, huF, ?_⟩
    by_contra hc
    push Not at hc
    exact hun (by
      unfold Paired; rw [h.pairs]
      exact (hS.paired_filter_iff huF).2 ⟨hc.1, fun x hx hux => hc.2 x hx hux.symm⟩)
  · rintro ⟨hu, huF, hc⟩
    refine ⟨⟨hu, huF⟩, fun hp => ?_⟩
    unfold Paired at hp
    rw [h.pairs] at hp
    obtain ⟨hpu, hpart⟩ := (hS.paired_filter_iff huF).1 hp
    rcases hc with hc | ⟨x, hx, hux⟩
    · exact hc hpu
    · exact hpart x hx hux.symm

/-- A paired parameter that is not the partner of a member of `F` stays paired. -/
theorem wt_eq_zero (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ} (hu : u ∉ S.unpaired)
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) : S'.wt u = 0 := by
  refine wt_of_notMem fun hu' => ?_
  obtain ⟨hup, -, hc⟩ := (h.mem_unpaired_iff hS).1 hu'
  rcases hc with hc | ⟨x, hx, hxu⟩
  · exact hu (mem_unpaired.2 ⟨hup, hc⟩)
  · exact hpart x hx hxu

/-- A parameter that no deletion of `T` reroutes to keeps at most its children outside `D`. -/
theorem wt_le_weight (h : Reduction f S S' F D T) {u : ℕ} (hT : ∀ N ∈ T, N ∉ S.children u) :
    S'.wt u ≤ weight (S.children u \ D.toFinset).card := by
  by_cases hu : u ∈ S'.unpaired
  · rw [wt_of_mem hu]
    refine weight_mono (Finset.card_le_card ?_)
    rcases h.children u (mem_unpaired.1 hu).1 with h' | ⟨N, hN, hNu⟩
    · exact h'
    · exact absurd hNu (hT N hN)
  · rw [wt_of_notMem hu]; exact Nat.zero_le _

/-- A parameter that no deletion of `T` reroutes to keeps at most its children outside `D`. -/
theorem children_subset (h : Reduction f S S' F D T) {u : ℕ} (hu : u ∈ S'.params)
    (hT : ∀ N ∈ T, N ∉ S.children u) : S'.children u ⊆ S.children u \ D.toFinset :=
  (h.children u hu).resolve_right fun ⟨N, hN, hNu⟩ => hT N hN hNu

/-- A parameter that is not the partner of a member of `F`, and that no deletion reroutes to,
does not gain weight. -/
theorem wt_le (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) (hT : ∀ N ∈ T, N ∉ S.children u) :
    S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · rw [wt_of_mem hu]
    exact (h.wt_le_weight hT).trans (weight_mono (Finset.card_le_card Finset.sdiff_subset))
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- A used parameter that is not the partner of a member of `F` gains at most one in weight. -/
private theorem wt_le_add_one (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) (hdeg : 1 ≤ S.deg u) : S'.wt u ≤ S.wt u + 1 := by
  by_cases hu : u ∈ S.unpaired
  · rw [wt_of_mem hu]
    have := six_le_weight hdeg
    have := S'.wt_le_seven u
    omega
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- A parameter all of whose children are deleted, and that no deletion reroutes to, becomes
unused. -/
theorem wt_eq_zero_of_subset (h : Reduction f S S' F D T) {u : ℕ}
    (hsub : S.children u ⊆ D.toFinset) (hT : ∀ N ∈ T, N ∉ S.children u) : S'.wt u = 0 := by
  have := h.wt_le_weight hT
  rwa [Finset.sdiff_eq_empty_iff_subset.2 hsub, Finset.card_empty, weight_zero,
    Nat.le_zero] at this

/-- An unpaired parameter does not gain weight when it has degree at least two if some deletion
may reroute to it. -/
theorem wt_le_wt (h : Reduction f S S' F D T) {u : ℕ} (hu : u ∈ S.unpaired)
    (hT : ∀ N ∈ T, N ∈ S.children u → 2 ≤ S.deg u) : S'.wt u ≤ S.wt u := by
  by_cases hu' : u ∈ S'.unpaired
  · rw [wt_of_mem hu]
    by_cases hN : ∃ N ∈ T, N ∈ S.children u
    · obtain ⟨N, hN, hNu⟩ := hN
      rw [weight_of_two_le (hT N hN hNu)]
      exact S'.wt_le_seven u
    · push Not at hN
      exact (h.wt_le_weight hN).trans
        (weight_mono (Finset.card_le_card Finset.sdiff_subset))
  · rw [wt_of_notMem hu']; exact Nat.zero_le _

/-- In an exclusive state, a parameter that is not the partner of a member of `F` does not gain
weight when every deletion that may reroute to it deletes a constraint with another parameter as a
parent. -/
theorem wt_le_of_exclusive (h : Reduction f S S' F D T) (hS : S.Valid f) (hexcl : S.Exclusive)
    {u : ℕ} (hpart : ∀ x ∈ F, ¬ S.IsPartner x u)
    (hT : ∀ N ∈ T, N ∈ S.children u → ∃ x ∈ S.params, x ≠ u ∧ N ∈ S.children x) :
    S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · exact h.wt_le_wt hu fun N hN hNu => by
      obtain ⟨x, hx, hxu, hNx⟩ := hT N hN hNu
      exact hexcl.two_le_deg hu hNu hx hxu hNx
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- **The potential of a reduction.** If every parameter outside `F` gains at most `gain` and
loses at least `loss` in weight, then
`W' + 2 |D| + 3 k + ∑_{x ∈ F} wt(x) + ∑ loss ≤ W + ∑ gain`, where `k` is the number of pairs
meeting `F`. -/
theorem W_le (h : Reduction f S S' F D T) (loss gain : ℕ → ℕ)
    (hpt : ∀ u ∈ S.params \ F, S'.wt u + loss u ≤ S.wt u + gain u) :
    S'.W + 2 * D.length + 3 * (S.pairsMeeting F).card + ∑ u ∈ F, S.wt u +
        ∑ u ∈ S.params \ F, loss u ≤ S.W + ∑ u ∈ S.params \ F, gain u := by
  have hW := W_add_le (S := S) (S' := S') (N := S.params) le_rfl
    (by rw [h.params]; exact Finset.sdiff_subset)
    (fun u => if u ∈ F then S.wt u else loss u) (fun u => if u ∈ F then 0 else gain u)
    fun u hu => by
      by_cases huF : u ∈ F
      · simp only [ite_eq_left huF, wt_of_notMem_params (show u ∉ S'.params by
          rw [h.params]; exact fun h' => (Finset.mem_sdiff.1 h').2 huF)]
        omega
      · simp only [ite_eq_right huF]
        exact hpt u (Finset.mem_sdiff.2 ⟨hu, huF⟩)
  have hsplit : ∀ g : ℕ → ℕ, ∑ u ∈ S.params, g u =
      ∑ u ∈ S.params \ F, g u + ∑ u ∈ F, g u := fun g => (Finset.sum_sdiff h.subset).symm
  rw [hsplit, hsplit (fun u => if u ∈ F then 0 else gain u),
    Finset.sum_congr rfl (g := fun u => loss u) fun u hu => ite_eq_right (Finset.mem_sdiff.1 hu).2,
    Finset.sum_congr rfl (g := fun u => S.wt u) fun u hu => ite_eq_left hu,
    Finset.sum_congr rfl (g := fun u => gain u) fun u hu => ite_eq_right (Finset.mem_sdiff.1 hu).2,
    Finset.sum_congr rfl (g := fun _ => 0) fun u hu => ite_eq_left hu, Finset.sum_const_zero] at hW
  have hs := h.s_add
  have hq := h.q_add
  omega

/-- A reduction restricting at most two parameters, and at least one parameter or constraint,
with `W' + 14 |F| ≤ W + 14 k`, is a step of gate elimination. -/
theorem step (h : Reduction f S S' F D T) (hS : S.Valid f) (hF : F.card ≤ 2)
    (hne : 0 < F.card + D.length)
    (hW : S'.W + 14 * F.card ≤ S.W + 14 * (S.pairsMeeting F).card) : Step f S S' := by
  have ha := h.a_add hS
  have hm := h.m_add
  have hs := h.s_add
  have hk := hS.card_pairsMeeting_le F
  exact ⟨h.valid, by omega, by omega, by omega, by omega⟩

/-- Deleting one constraint with at most two parameters as parents is a step of gate
elimination: only those parents may gain weight, each at most one. -/
theorem step_of_delete {N : ℕ ⊕ ℕ} (h : Reduction f S S' ∅ [N] [N]) (hS : S.Valid f)
    (hN : (S.params.filter fun u => N ∈ S.children u).card ≤ 2) : Step f S S' := by
  refine h.step hS (by simp) (by simp) ?_
  have hW := h.W_le (fun _ => 0) (fun u => if N ∈ S.children u then 1 else 0) fun u hu => by
    by_cases hNu : N ∈ S.children u
    · rw [ite_eq_left hNu]
      exact Nat.add_le_add_right (h.wt_le_add_one hS (fun _ hx => absurd hx (Finset.notMem_empty _))
        (Finset.card_pos.2 ⟨N, hNu⟩)) 0
    · rw [ite_eq_right hNu]
      exact Nat.add_le_add_right (h.wt_le hS (fun _ hx => absurd hx (Finset.notMem_empty _))
        fun N' hN' => by rw [List.mem_singleton] at hN'; exact hN' ▸ hNu) 0
  rw [Finset.sdiff_empty, ← Finset.card_filter] at hW
  simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.length_singleton,
    mul_zero, add_zero] at hW ⊢
  omega

end Reduction

/-! ### Restrictions -/

/-- Restricting a parameter `x` to a constant, or to a literal of a remaining parameter `y` with
at least the children of `x` and, if `x` is paired, its partner, is a reduction. -/
theorem Valid.reduction_restrict {S : State n} (hS : S.Valid f) {x : ℕ} (hx : x ∈ S.params)
    {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x ∧ S.children x ⊆ S.children y ∧
      (S.Paired x → S.IsPartner x y)) :
    Reduction f S (S.restrict x ℓ (S.pairsAvoid x)) {x} [] [] where
  valid := hS.restrict
    { mem := hx
      reads := fun y hy => ⟨(hℓ y hy).1, (hℓ y hy).2.1⟩
      subset := Finset.filter_subset _ _
      avoid := fun pr hpr => (Finset.mem_filter.1 hpr).2
      drop := fun pr hpr hP => by
        have hprx : pr.1 = x ∨ pr.2 = x := by
          by_contra hc
          push Not at hc
          exact hP (Finset.mem_filter.2 ⟨hpr, hc⟩)
        refine ⟨hprx, fun y hy => ?_⟩
        obtain ⟨pr', hpr', hxy⟩ := (hℓ y hy).2.2.2 ⟨pr, hpr, hprx⟩
        have := hS.pair_unique hpr hpr' hprx
          (by rcases hxy with h | h; exacts [Or.inl h.1, Or.inr h.1])
        subst this
        rcases hxy with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inr h.symm
        · exact Or.inl h.symm }
  subset := Finset.singleton_subset_iff.2 hx
  params := by
    ext u
    simp only [restrict_params, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
    tauto
  pairs := Finset.filter_congr fun pr _ => by simp only [Finset.mem_singleton, not_or]
  size := by rw [List.length_nil, add_zero]; rfl
  children u hu := by
    refine Or.inl ?_
    rw [List.toFinset_nil, Finset.sdiff_empty, restrict_children]
    have hux : u ≠ x := Finset.ne_of_mem_erase hu
    by_cases hℓu : ℓ.Reads u
    · exact (SemiCircuit.children_subst_subset x ℓ u).trans
        (Finset.union_subset le_rfl (hℓ u hℓu).2.2.1)
    · rw [SemiCircuit.children_subst hux hℓu]
  deletable N _ hN := by
    rcases N with J | e
    · exact ⟨hN.1, Gate.degenerate_subst hN.2 _ _⟩
    · exact ⟨hN.1, Equation.card_subst_le.trans hN.2⟩

/-! ### Fixing a parameter to a constant -/

/-- Fix the parameter `w` to the constant `b`, dropping the pair containing `w`, if any: the
restriction (UF) for an unpaired parameter and (PF) for a paired one. -/
def fixConst (S : State n) (w : ℕ) (b : Bool) : State n :=
  S.restrict w (Lit.const b) (S.pairsAvoid w)

private theorem restrictOK_fixConst {S : State n} {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    S.RestrictOK w (Lit.const b) (S.pairsAvoid w) where
  mem := hw
  reads y hy := by simp [Lit.Reads, Lit.const] at hy
  subset := Finset.filter_subset _ _
  avoid pr hpr := (Finset.mem_filter.1 hpr).2
  drop pr hpr hP := by
    refine ⟨?_, fun y hy => by simp [Lit.Reads, Lit.const] at hy⟩
    by_contra h
    push Not at h
    exact hP (Finset.mem_filter.2 ⟨hpr, h⟩)

/-- Fixing a parameter to a constant preserves validity. -/
theorem Valid.fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    (S.fixConst w b).Valid f :=
  hS.restrict (restrictOK_fixConst hw b)

/-- Fixing `w` to a constant removes `w` from `S.params`. -/
@[simp] theorem fixConst_params (S : State n) (w : ℕ) (b : Bool) :
    (S.fixConst w b).params = S.params.erase w := rfl

/-- Fixing `w` to a constant retains the pairs avoiding `w`. -/
@[simp] theorem fixConst_pairs (S : State n) (w : ℕ) (b : Bool) :
    (S.fixConst w b).pairs = S.pairsAvoid w := rfl

/-- Fixing a parameter to a constant preserves the size of the state. -/
theorem fixConst_size (S : State n) (w : ℕ) (b : Bool) : (S.fixConst w b).size = S.size := rfl

/-- Fixing `w` to `b` substitutes `w` with `Lit.const b` in every gate. -/
@[simp] theorem fixConst_gate (S : State n) (w : ℕ) (b : Bool) (J : ℕ) :
    (S.fixConst w b).gate J = (S.gate J).subst w (Lit.const b) := rfl

/-- Fixing `w` to a constant preserves the children of every `z ≠ w`. -/
theorem fixConst_children (S : State n) {w : ℕ} (b : Bool) {z : ℕ} (hz : z ≠ w) :
    (S.fixConst w b).children z = S.children z :=
  SemiCircuit.children_subst hz (by simp [Lit.const])

/-- Fixing a parameter to a constant is a reduction. -/
theorem Valid.reduction_fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params)
    (b : Bool) : Reduction f S (S.fixConst w b) {w} [] [] :=
  hS.reduction_restrict hw fun y hy => by simp [Lit.Reads, Lit.const] at hy

/-! ### Deletions -/

/-- Deleting a gate is a reduction; it may reroute only to the parameter read by the literal. -/
theorem Valid.reduction_deleteGate {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) {T : List (ℕ ⊕ ℕ)} (hT : ∀ t, ℓ.Reads t → .inl J ∈ T) :
    Reduction f S (S.deleteGate J ℓ) ∅ [.inl J] T where
  valid := hS.deleteGate h
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := deleteGate_size h
  children u hu := by
    by_cases hℓu : ℓ.Reads u
    · exact Or.inr ⟨_, hT u hℓu, (SemiCircuit.inl_mem_children _).2 ⟨h.mem, h.reads u hℓu⟩⟩
    · refine Or.inl ?_
      rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.sdiff_singleton_eq_erase]
      exact deleteGate_children_of_ne hS h hu hℓu
  deletable N hN hdel := by
    rcases N with K | e
    · have hKJ : K ≠ J := fun he => hN (by rw [he]; exact List.mem_singleton_self _)
      exact ⟨Finset.mem_erase.2 ⟨hKJ, hdel.1⟩, Gate.degenerate_subst hdel.2 _ _⟩
    · exact ⟨hdel.1, Equation.card_subst_le.trans hdel.2⟩

/-- Deleting a gate that is constant on the solutions of the affine system is a reduction
rerouting nothing. -/
theorem Valid.reduction_deleteConst {S : State n} (hS : S.Valid f) {J : ℕ} {c : Bool}
    (hJ : J ∈ S.gates) (hc : ∀ val, S.EqnsHold val → (S.gate J).eval val = c) :
    Reduction f S (S.deleteGate J (Lit.const c)) ∅ [.inl J] [] :=
  hS.reduction_deleteGate ⟨hJ, fun t ht => by simp [Lit.Reads, Lit.const] at ht,
    Or.inl fun val hval => by rw [hc val hval, Lit.eval_const]⟩
    fun t ht => by simp [Lit.Reads, Lit.const] at ht

/-- Deleting an equation `v = ℓ` is a reduction; it may reroute only to the parameter read by
the literal. -/
theorem Valid.reduction_deleteEqn {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) {T : List (ℕ ⊕ ℕ)} (hT : ∀ t, ℓ.Reads t → .inr e ∈ T) :
    Reduction f S (S.deleteEqn e v ℓ) ∅ [.inr e] T where
  valid := hS.deleteEqn h
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := deleteEqn_size h
  children u hu := by
    by_cases hℓu : ℓ.Reads u
    · exact Or.inr ⟨_, hT u hℓu, (SemiCircuit.inr_mem_children _).2
        ⟨h.mem, (h.reads u hℓu).1⟩⟩
    · refine Or.inl ?_
      rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.sdiff_singleton_eq_erase]
      exact deleteEqn_children_of_ne hS h hu hℓu
  deletable N hN hdel := by
    rcases N with K | e'
    · exact ⟨hdel.1, Gate.degenerate_subst hdel.2 _ _⟩
    · have hee : e' ≠ e := fun he => hN (by rw [he]; exact List.mem_singleton_self _)
      exact ⟨Finset.mem_erase.2 ⟨hee, hdel.1⟩, Equation.card_subst_le.trans hdel.2⟩

/-- Deleting an equation without terms is a reduction rerouting nothing. -/
private theorem Valid.reduction_dropTrivialEqn {S : State n} (hS : S.Valid f) {e : ℕ}
    (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : Reduction f S (S.dropTrivialEqn e) ∅ [.inr e] [] where
  valid := hS.dropTrivialEqn he hterms
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := dropTrivialEqn_size he
  children u _ := Or.inl (by
    rw [dropTrivialEqn_children, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.sdiff_singleton_eq_erase])
  deletable N hN hdel := by
    rcases N with K | e'
    · exact hdel
    · have hee : e' ≠ e := fun h => hN (by rw [h]; exact List.mem_singleton_self _)
      exact ⟨Finset.mem_erase.2 ⟨hee, hdel.1⟩, hdel.2⟩

/-- In a valid state, an equation whose terms are all parameters has no terms. -/
theorem Valid.terms_eq_empty_of_subset {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hsub : (S.eqn e).terms ⊆ S.params) : (S.eqn e).terms = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨val, hval, heq⟩ := hS.wf.solvable 0
  obtain ⟨val', hval', heq'⟩ := hS.wf.solvable (Function.update val x (!val x))
  have h1 := heq e he
  have h2 := heq' e he
  unfold Equation.Holds at h1 h2
  rw [← Finset.add_sum_erase _ _ hx] at h1 h2
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hval' i (hsub (Finset.mem_of_mem_erase hi)),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)], hval' x (hsub hx),
    Function.update_self, ← h1] at h2
  cases val x <;> simp at h2

/-- A deletable constraint of a valid state is deleted by a reduction. -/
theorem Valid.exists_reduction_delete {S : State n} (hS : S.Valid f) {N : ℕ ⊕ ℕ}
    (hN : S.Deletable N) : ∃ S', Reduction f S S' ∅ [N] [N] := by
  rcases N with J | e
  · obtain ⟨hJ, hdeg⟩ := hN
    exact ⟨_, hS.reduction_deleteGate (ℓ := (S.gate J).lit)
      ⟨hJ, fun t ht => Gate.reads_of_lit_reads ht, Or.inl fun val _ => Gate.eval_lit hdeg val⟩
      fun _ _ => List.mem_singleton_self _⟩
  · obtain ⟨he, hcard⟩ := hN
    by_cases haux : ∃ v ∈ (S.eqn e).terms, v ∈ S.aux
    · obtain ⟨v, hv, hva⟩ := haux
      have hrest : ((S.eqn e).terms.erase v).card ≤ 1 := by
        rw [Finset.card_erase_of_mem hv]; omega
      rcases Finset.card_le_one_iff_subset_singleton.1 hrest with ⟨U, hU⟩
      by_cases hUmem : U ∈ (S.eqn e).terms.erase v
      · -- the equation reads `v + U = rhs`
        have hterms : (S.eqn e).terms = {v, U} := by
          ext i
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hi
            by_cases hiv : i = v
            · exact Or.inl hiv
            · exact Or.inr (Finset.mem_singleton.1 (hU (Finset.mem_erase.2 ⟨hiv, hi⟩)))
          · rintro (rfl | rfl)
            · exact hv
            · exact Finset.mem_of_mem_erase hUmem
        have hUv : U ≠ v := Finset.ne_of_mem_erase hUmem
        refine ⟨_, hS.reduction_deleteEqn (v := v) (ℓ := ⟨.node U, (S.eqn e).rhs⟩)
          ⟨he, hva, fun val => ?_, fun t ht => ?_⟩ fun _ _ => List.mem_singleton_self _⟩
        · unfold Equation.Holds
          rw [hterms, Finset.sum_pair hUv.symm]
          simp only [Lit.eval, Arg.eval_node]
          generalize val v = a; generalize val U = b; generalize (S.eqn e).rhs = r
          revert a b r; decide
        · cases ht
          exact ⟨Finset.mem_of_mem_erase hUmem, hUv⟩
      · -- the equation reads `v = rhs`
        have hterms : (S.eqn e).terms = {v} := by
          ext i
          simp only [Finset.mem_singleton]
          constructor
          · intro hi
            by_contra hiv
            have := hU (Finset.mem_erase.2 ⟨hiv, hi⟩)
            rw [Finset.mem_singleton] at this
            exact hUmem (this ▸ Finset.mem_erase.2 ⟨hiv, hi⟩)
          · rintro rfl; exact hv
        refine ⟨_, hS.reduction_deleteEqn (v := v) (ℓ := Lit.const (S.eqn e).rhs)
          ⟨he, hva, fun val => ?_, fun t ht => by cases ht⟩ fun _ ht => by cases ht⟩
        unfold Equation.Holds
        rw [hterms, Finset.sum_singleton, Lit.eval_const]
    · push Not at haux
      have hsub : (S.eqn e).terms ⊆ S.params := fun i hi => by
        rcases Finset.mem_union.1 (hS.wf.terms_subset e he hi) with hp | ha
        · exact hp
        · exact absurd ha (haux i hi)
      exact ⟨_, (hS.reduction_dropTrivialEqn he (hS.terms_eq_empty_of_subset he hsub)).mono
        fun _ hN => absurd hN List.not_mem_nil⟩

/-- Distinct deletable constraints of a valid state are deleted by a reduction. -/
theorem Valid.exists_reduction_deleteAll {S : State n} (hS : S.Valid f) (l : List (ℕ ⊕ ℕ))
    (hl : l.Nodup) (hdel : ∀ N ∈ l, S.Deletable N) : ∃ S', Reduction f S S' ∅ l l := by
  induction l generalizing S with
  | nil => exact ⟨S, Reduction.refl hS⟩
  | cons N l ih =>
    obtain ⟨S₁, h₁⟩ := hS.exists_reduction_delete (hdel N List.mem_cons_self)
    have hl' := List.nodup_cons.1 hl
    obtain ⟨S', h₂⟩ := ih h₁.valid hl'.2 fun N' hN' => h₁.deletable N'
      (by rw [List.mem_singleton]; rintro rfl; exact hl'.1 hN')
      (hdel N' (List.mem_cons_of_mem _ hN'))
    have h := h₁.trans h₂
    rw [Finset.empty_union] at h
    exact ⟨S', h⟩

end State

end Cslib.Circuits.Boolean.AffineDisperser
