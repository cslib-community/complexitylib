/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Normal

/-!
# Restructuring to a minimal AND

Section 4.2 of [Mishra and Santhanam][MishraSanthanam2026]. In a normal state with
`d < a` (`State.Normal`), the minimal gate is an AND-type gate `G` on two distinct inputs among
the parameters and auxiliary variables (`State.Valid.exists_minGate`).

*Restructuring* (Section 4.2) uses preparatory operations (`State.Preparation`), which keep `m`,
`s` and `q` and do not increase `W`. An auxiliary input of `G` is exchanged with a parameter it
depends on by the affine reparameterisation (`State.Valid.exists_preparation_auxIn_lt`), and a
child of `G` reading an input of `G` is relabelled to read both inputs instead
(`State.Valid.exists_preparation_childIn_lt`). Afterwards `G` is a *minimal AND*
(`State.MinimalAnd`, `State.Valid.exists_minimalAnd`): it reads two unpaired parameters `x` and
`y` with `2 ≤ deg y ≤ deg x`, no child of `G` reads them, and `G` is not the output and has a
child.

*Elimination* of the minimal AND (Section 4.3, `State.Valid.step_of_minimalAnd`) is in
`Complexity/Computability/Circuit/Boolean/AffineDisperser/Elimination.lean`.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.auxArgs`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.auxIn`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.childIn`: the measures of the restructuring.
* `Cslib.Circuits.Boolean.AffineDisperser.State.MinimalAnd`: the minimal AND.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_preparation_auxIn_lt`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_preparation_childIn_lt`: the
  restructuring.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_minimalAnd`: the restructured minimal
  gate is a minimal AND (`MinimalAnd`), eliminated in `Elimination.lean`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Exchanging a parameter and an auxiliary variable -/

/-- An auxiliary variable of a valid state occurs in some equation: otherwise the affine system
would not determine it. -/
private theorem Valid.exists_eqn_of_aux {S : State n} (hS : S.Valid f) {v : ℕ} (hv : v ∈ S.aux) :
    ∃ e ∈ S.eqns, v ∈ (S.eqn e).terms := by
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hS.wf.solvable 0
  have hvp : v ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp hv
  have heq' : S.EqnsHold (Function.update val v (!val v)) := fun e he =>
    (Equation.holds_congr fun i hi =>
      Function.update_of_ne (show i ≠ v from fun h => hne e he (h ▸ hi)) _ _).2 (heq e he)
  have := hS.wf.unique val _ (fun j hj => (Function.update_of_ne
    (show j ≠ v from fun h => hvp (h ▸ hj)) _ _).symm) heq heq' v hv
  rw [Function.update_self] at this
  cases h : val v <;> simp [h] at this

/-- The affine reparameterisation of an unpaired parameter `x` of degree at least two and an
auxiliary variable `Q` of degree at least two depending on it is a preparatory operation: it keeps
every child, and both weights are `7`. -/
private theorem Valid.preparation_swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool}
    {T : Finset ℕ} (hx : x ∈ S.unpaired) (hxdeg : 2 ≤ S.deg x) (hQ : Q ∈ S.aux)
    (hQdeg : 2 ≤ S.deg Q) (haff : S.AffineIn Q c T) (hxT : x ∈ T) :
    Preparation f S (S.swap x Q c T) := by
  obtain ⟨hxp, hxu⟩ := mem_unpaired.1 hx
  have hok : S.SwapOK x Q c T := ⟨hxp, hxu, hQ, haff, hxT⟩
  have hQp : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp hQ
  have hQx : Q ≠ x := fun h => hQp (h ▸ hxp)
  set S₁ := S.swap x Q c T
  have hm : S₁.m = S.m := by
    change (insert Q (S.params.erase x)).card = S.params.card
    rw [Finset.card_insert_of_notMem fun h => hQp (Finset.mem_of_mem_erase h),
      Finset.card_erase_add_one hxp]
  refine ⟨hS.swap hok, hm, rfl, rfl, ?_⟩
  have hN : S.params ⊆ insert Q S.params := Finset.subset_insert _ _
  have hN' : S₁.params ⊆ insert Q S.params :=
    Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  have hpt : ∀ u ∈ insert Q S.params, S₁.wt u + (if u = x then 7 else 0) ≤
      S.wt u + (if u = Q then 7 else 0) := by
    intro u _
    by_cases hux : u = x
    · subst hux
      rw [wt_of_notMem_params (by simp [S₁, hQx.symm]), wt_of_mem hx, weight_of_two_le hxdeg,
        ite_eq_left rfl, ite_eq_right hQx.symm]
    · rw [ite_eq_right hux]
      by_cases huQ : u = Q
      · subst huQ
        rw [ite_eq_left rfl, wt_of_notMem_params hQp]
        have := S₁.wt_le_seven u
        omega
      · rw [ite_eq_right huQ]
        by_cases hu₁ : u ∈ S₁.unpaired
        · have hus : u ∈ S.unpaired := by
            obtain ⟨hup, hun⟩ := mem_unpaired.1 hu₁
            simp only [S₁, swap_params, Finset.mem_insert, Finset.mem_erase] at hup
            exact mem_unpaired.2 ⟨(hup.resolve_left huQ).2, hun⟩
          rw [wt_of_mem hu₁, wt_of_mem hus]
          rfl
        · rw [wt_of_notMem hu₁]; omega
  have hW := W_add_le hN hN' _ _ hpt
  rw [Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_of_mem hxp),
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_insert_self _ _)] at hW
  have hs : S₁.s = S.s := rfl
  have hq : S₁.q = S.q := rfl
  omega

/-! ### Rewiring a gate -/

/-- Rewiring a gate to a gate reading only parameters of degree at least two is a preparatory
operation: only those parameters may gain a child, and their weight is already `7`. -/
private theorem Valid.preparation_rewire {S : State n} (hS : S.Valid f) {J : ℕ} {g : Gate}
    (h : S.RewireOK J g) (hdeg : ∀ t, g.Reads t → t ∈ S.unpaired → 2 ≤ S.deg t) :
    Preparation f S (S.rewire J g) := by
  refine ⟨hS.rewire h, rfl, rfl, rfl, ?_⟩
  have hpt : ∀ u ∈ S.params, (S.rewire J g).wt u + 0 ≤ S.wt u + 0 := by
    intro u hu
    by_cases hu' : u ∈ S.unpaired
    · have hu₁ : u ∈ (S.rewire J g).unpaired := by rwa [unpaired_congr rfl rfl]
      rw [wt_of_mem hu₁, wt_of_mem hu']
      by_cases hgu : g.Reads u
      · rw [weight_of_two_le (hdeg u hgu hu')]
        have := weight_le_seven ((S.rewire J g).deg u)
        omega
      · refine Nat.add_le_add_right (weight_mono (Finset.card_le_card fun w hw => ?_)) _
        rcases w with K | e
        · rw [inl_mem_children_rewire] at hw
          obtain ⟨hK, hr⟩ := hw
          by_cases hKJ : K = J
          · rw [ite_eq_left hKJ] at hr; exact absurd hr hgu
          · rw [ite_eq_right hKJ] at hr
            exact (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
        · rwa [inr_mem_children_rewire] at hw
    · rw [wt_of_notMem (by rwa [unpaired_congr rfl rfl]), wt_of_notMem hu']
  have hW := W_add_le (S := S) (S' := S.rewire J g) le_rfl le_rfl _ _ hpt
  have hs : (S.rewire J g).s = S.s := rfl
  have hq : (S.rewire J g).q = S.q := rfl
  simp only [Finset.sum_const_zero] at hW
  omega

/-! ### Degenerate minimal gates allow deletions -/

private theorem deletionAvailable_of_degenerate {S : State n} {J : ℕ} (hJ : J ∈ S.gates)
    (h : (S.gate J).Degenerate) : S.DeletionAvailable :=
  Or.inr (Or.inl ⟨J, hJ, (S.gate J).lit, fun _ ht => Gate.reads_of_lit_reads ht,
    fun val _ => Gate.eval_lit h val⟩)

/-- A gate one of whose inputs is constant on the solutions of the affine system allows (D1). -/
private theorem deletionAvailable_of_const_input {S : State n} {J t : ℕ} (hJ : J ∈ S.gates)
    {c : Bool}
    (ht : (S.gate J).Reads t) (hc : ∀ val, S.EqnsHold val → val t = c) : S.DeletionAvailable := by
  refine Or.inr (Or.inl ⟨J, hJ, ?_⟩)
  rcases ht with ht | ht
  · refine ⟨unaryLit ((S.gate J).op c) (S.gate J).right,
      fun s hs => Or.inr (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [ht, Arg.eval_node, hc val hval]
  · refine ⟨unaryLit (fun a => (S.gate J).op a c) (S.gate J).left,
      fun s hs => Or.inl (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [ht, Arg.eval_node, hc val hval]

/-- A gate whose inputs differ by a constant on the solutions of the affine system allows
(D1). -/
private theorem deletionAvailable_of_dependent {S : State n} {J t t' : ℕ} (hJ : J ∈ S.gates)
    {c : Bool}
    (hargs : ((S.gate J).left = .node t ∧ (S.gate J).right = .node t') ∨
      ((S.gate J).left = .node t' ∧ (S.gate J).right = .node t))
    (hc : ∀ val, S.EqnsHold val → val t' = (val t ^^ c)) : S.DeletionAvailable := by
  refine Or.inr (Or.inl ⟨J, hJ, ?_⟩)
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine ⟨unaryLit (fun a => (S.gate J).op a (a ^^ c)) (S.gate J).left,
      fun s hs => Or.inl (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [hl, hr, Arg.eval_node, Arg.eval_node, hc val hval]
  · refine ⟨unaryLit (fun a => (S.gate J).op (a ^^ c) a) (S.gate J).right,
      fun s hs => Or.inr (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [hl, hr, Arg.eval_node, Arg.eval_node, hc val hval]

/-! ### The minimal gate of a normal state -/

/-- The output of a valid state with `d < a` is not a literal of an auxiliary variable. -/
private theorem Valid.not_out_reads_aux {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {v : ℕ} (hv : v ∈ S.aux) : ¬ S.out.Reads v := by
  intro hr
  obtain ⟨c, T, hT⟩ := hS.wf.exists_affineIn hv
  refine hS.out_not_affine hf ha (c ^^ S.out.neg) hT.1 fun val hval => ?_
  unfold Lit.eval
  unfold Lit.Reads at hr
  rw [hr, Arg.eval_node, hT.2 val hval.1]
  generalize ∑ j ∈ T, val j = s
  cases c <;> cases s <;> cases S.out.neg <;> rfl

/-- In a valid state with `d < a` where no affine gate can be moved and no deletion applies,
there are gates, and the minimal one is an AND-type gate reading two distinct inputs among the
parameters and auxiliary variables. -/
theorem Valid.exists_minGate {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) (hmov : ∀ J, ¬ S.Movable J) (hdel : ¬ S.DeletionAvailable) :
    ∃ h : S.gates.Nonempty, ¬ IsAffineOp (S.gate (S.gates.min' h)).op ∧
      ∃ t₁ t₂, (S.gate (S.gates.min' h)).left = .node t₁ ∧
        (S.gate (S.gates.min' h)).right = .node t₂ ∧ t₁ ≠ t₂ ∧
        t₁ ∈ S.params ∪ S.aux ∧ t₂ ∈ S.params ∪ S.aux := by
  have hne : S.gates.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rcases hout : S.out.arg with b | t
    · refine hS.out_not_affine hf ha (b ^^ S.out.neg) (Finset.empty_subset _) fun val _ => ?_
      simp [Lit.eval, hout]
    · have hlive := hS.wf.out_live t hout
      simp only [SemiCircuit.live, Finset.mem_union, hempty, Finset.notMem_empty, or_false]
        at hlive
      rcases hlive with hp | hv
      · exact hS.not_out_reads_param hf ha hp hout
      · exact hS.not_out_reads_aux hf ha hv hout
  set G := S.gates.min' hne
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  have hmin : ∀ i, (S.gate G).Reads i → i ∉ S.gates := fun i hi hig =>
    absurd (hS.wf.reads_lt G hG i hig hi) (not_lt.2 (Finset.min'_le _ _ hig))
  have hand : ¬ IsAffineOp (S.gate G).op := fun haff => hmov G ⟨hG, haff, hmin⟩
  have hpa : ∀ i, (S.gate G).Reads i → i ∈ S.params ∪ S.aux := fun i hi => by
    have := hS.wf.reads_live G hG i hi
    simp only [SemiCircuit.live, Finset.mem_union] at this ⊢
    rcases this with h | h
    · exact h
    · exact absurd h (hmin i hi)
  refine ⟨hne, hand, ?_⟩
  rcases hl : (S.gate G).left with b₁ | t₁
  · exact absurd (deletionAvailable_of_degenerate hG (Or.inl ⟨b₁, hl⟩)) hdel
  rcases hr : (S.gate G).right with b₂ | t₂
  · exact absurd (deletionAvailable_of_degenerate hG (Or.inr (Or.inl ⟨b₂, hr⟩))) hdel
  refine ⟨t₁, t₂, rfl, rfl, fun he => ?_, hpa t₁ (Or.inl hl), hpa t₂ (Or.inr hr)⟩
  subst he
  exact hdel (deletionAvailable_of_degenerate hG (Or.inr (Or.inr (hl.trans hr.symm))))

/-- An auxiliary input `Q` of the minimal gate depends on a parameter `x` other than the other
input; when no preliminary reduction applies, `x` is unpaired of degree at least two, and `Q` has
degree at least two. -/
private theorem Valid.exists_param_of_aux_input {S : State n} (hS : S.Valid f) (hN : S.Normal)
    {G Q o : ℕ}
    (hG : G ∈ S.gates) (hargs : ((S.gate G).left = .node Q ∧ (S.gate G).right = .node o) ∨
      ((S.gate G).left = .node o ∧ (S.gate G).right = .node Q))
    (hQ : Q ∈ S.aux) (hQo : Q ≠ o) :
    ∃ x c T, S.AffineIn Q c T ∧ x ∈ T ∧ x ≠ o ∧ x ∈ S.unpaired ∧ 2 ≤ S.deg x ∧
      2 ≤ S.deg Q := by
  obtain ⟨c, T, hT⟩ := hS.wf.exists_affineIn hQ
  have hQp : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp hQ
  have hGQ : (S.gate G).Reads Q := (Gate.reads_of_args hargs).1
  by_cases hTo : ∃ x ∈ T, x ≠ o
  · obtain ⟨x, hxT, hxo⟩ := hTo
    obtain ⟨e, he, hxe⟩ := hT.mem_terms hS.wf hQp hxT
    obtain ⟨hxu, hxdeg⟩ := hN.system_param x (hT.1 hxT) e he hxe
    obtain ⟨e', he', hQe'⟩ := hS.exists_eqn_of_aux hQ
    have hQdeg : 2 ≤ S.deg Q := by
      have hsub : ({Sum.inr e', Sum.inl G} : Finset (ℕ ⊕ ℕ)) ⊆ S.children Q := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact (SemiCircuit.inr_mem_children _).2 ⟨he', hQe'⟩
        · exact (SemiCircuit.inl_mem_children _).2 ⟨hG, hGQ⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair (by simp)] at this
    exact ⟨x, c, T, hT, hxT, hxo, hxu, hxdeg, hQdeg⟩
  · push Not at hTo
    exfalso
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact hN.no_deletion (deletionAvailable_of_const_input hG hGQ (c := c) fun val hval => by
        rw [hT.2 val hval, Finset.sum_empty, add_zero])
    · have hxo := hTo x hx
      subst hxo
      have hTo' : T = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, hTo⟩
      refine hN.no_deletion (deletionAvailable_of_dependent hG (t := x) (t' := Q) (c := c) ?_
        fun val hval => ?_)
      · rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
        · exact Or.inr ⟨hl, hr⟩
        · exact Or.inl ⟨hl, hr⟩
      · rw [hT.2 val hval, hTo', Finset.sum_singleton]
        cases c <;> cases val x <;> rfl

/-! ### The measures of the restructuring -/

/-- The number of auxiliary inputs of a gate. -/
def auxArgs (S : State n) (g : Gate) : ℕ :=
  (match g.left with | .node t => if t ∈ S.aux then 1 else 0 | .const _ => 0) +
    (match g.right with | .node t => if t ∈ S.aux then 1 else 0 | .const _ => 0)

/-- The number of auxiliary inputs of the minimal gate. -/
def auxIn (S : State n) : ℕ :=
  if h : S.gates.Nonempty then S.auxArgs (S.gate (S.gates.min' h)) else 0

/-- The number of children of the minimal gate reading one of its parameter inputs. -/
def childIn (S : State n) : ℕ :=
  if h : S.gates.Nonempty then
    (S.gates.filter fun K => (S.gate K).Reads (S.gates.min' h) ∧
      ∃ t ∈ S.params, (S.gate (S.gates.min' h)).Reads t ∧ (S.gate K).Reads t).card
  else 0

private theorem auxIn_eq {S : State n} (hne : S.gates.Nonempty) :
    S.auxIn = S.auxArgs (S.gate (S.gates.min' hne)) := by
  simp only [auxIn, dite_eq_left hne]

private theorem auxArgs_nodes (S : State n) {g : Gate} {t₁ t₂ : ℕ} (hl : g.left = .node t₁)
    (hr : g.right = .node t₂) :
    S.auxArgs g = (if t₁ ∈ S.aux then 1 else 0) + (if t₂ ∈ S.aux then 1 else 0) := by
  simp only [auxArgs, hl, hr]

private theorem childIn_eq {S : State n} (hne : S.gates.Nonempty) :
    S.childIn = (S.gates.filter fun K => (S.gate K).Reads (S.gates.min' hne) ∧
      ∃ t ∈ S.params, (S.gate (S.gates.min' hne)).Reads t ∧ (S.gate K).Reads t).card := by
  simp only [childIn, dite_eq_left hne]

/-! ### Restructuring the minimal AND -/

/-- Exchanging an auxiliary input of the minimal gate of a normal state with a parameter it
depends on is a preparatory operation lowering the number of auxiliary inputs of the minimal
gate. -/
theorem Valid.exists_preparation_auxIn_lt {S : State n} (hS : S.Valid f) (hN : S.Normal)
    (hne : S.gates.Nonempty) {Q o : ℕ}
    (hargs : ((S.gate (S.gates.min' hne)).left = .node Q ∧
        (S.gate (S.gates.min' hne)).right = .node o) ∨
      ((S.gate (S.gates.min' hne)).left = .node o ∧ (S.gate (S.gates.min' hne)).right = .node Q))
    (hQ : Q ∈ S.aux) (hQo : Q ≠ o) :
    ∃ S₁ : State n, Preparation f S S₁ ∧ S₁.gates = S.gates ∧ S₁.auxIn < S.auxIn := by
  set G := S.gates.min' hne
  obtain ⟨x, c, T, hT, hxT, hxo, hxu, hxdeg, hQdeg⟩ :=
    hS.exists_param_of_aux_input hN (Finset.min'_mem _ _) hargs hQ hQo
  refine ⟨S.swap x Q c T, hS.preparation_swap hxu hxdeg hQ hQdeg hT hxT, rfl, ?_⟩
  set S₁ := S.swap x Q c T
  have hxp := (mem_unpaired.1 hxu).1
  have hQx : Q ≠ x := fun h => hS.wf.notMem_aux_of_mem_params (h ▸ hxp) hQ
  have hQ₁ : Q ∉ S₁.aux := fun h => by
    change Q ∈ insert x (S.aux.erase Q) at h
    rcases Finset.mem_insert.1 h with h | h
    · exact hQx h
    · exact Finset.notMem_erase _ _ h
  have ho₁ : o ∈ S₁.aux ↔ o ∈ S.aux := by
    change o ∈ insert x (S.aux.erase Q) ↔ _
    rw [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h.symm hxo
      · exact h
    · exact fun h => Or.inr ⟨hQo.symm, h⟩
  rw [auxIn_eq (S := S₁) hne, auxIn_eq hne]
  change S₁.auxArgs (S.gate G) < S.auxArgs (S.gate G)
  rcases hargs with ⟨hlQ, hro⟩ | ⟨hlo, hrQ⟩
  · rw [auxArgs_nodes S₁ hlQ hro, auxArgs_nodes S hlQ hro, ite_eq_right hQ₁, ite_eq_left hQ]
    by_cases hoa : o ∈ S.aux
    · rw [ite_eq_left (ho₁.2 hoa), ite_eq_left hoa]; omega
    · rw [ite_eq_right (fun h => hoa (ho₁.1 h)), ite_eq_right hoa]; omega
  · rw [auxArgs_nodes S₁ hlo hrQ, auxArgs_nodes S hlo hrQ, ite_eq_right hQ₁, ite_eq_left hQ]
    by_cases hoa : o ∈ S.aux
    · rw [ite_eq_left (ho₁.2 hoa), ite_eq_left hoa]; omega
    · rw [ite_eq_right (fun h => hoa (ho₁.1 h)), ite_eq_right hoa]; omega

/-- Rerouting a child `K` of the minimal gate that reads one of its parameter inputs, by
relabelling `K` with the operation it computes on the two inputs, is a preparatory operation
lowering the number of such children. -/
theorem Valid.exists_preparation_childIn_lt {S : State n} (hS : S.Valid f)
    (hne : S.gates.Nonempty) {t₁ t₂ : ℕ} (hl : (S.gate (S.gates.min' hne)).left = .node t₁)
    (hr : (S.gate (S.gates.min' hne)).right = .node t₂) (ht12 : t₁ ≠ t₂) (hx : t₁ ∈ S.params)
    (hy : t₂ ∈ S.params) (hxdeg : 2 ≤ S.deg t₁) (hydeg : 2 ≤ S.deg t₂) {K : ℕ}
    (hK : K ∈ S.gates) (hKG : (S.gate K).Reads (S.gates.min' hne))
    (hKt : (S.gate K).Reads t₁ ∨ (S.gate K).Reads t₂) :
    ∃ S₁ : State n, Preparation f S S₁ ∧ S₁.gates = S.gates ∧ S₁.auxIn = S.auxIn ∧
      S₁.childIn < S.childIn := by
  set G := S.gates.min' hne
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  have hGp : ∀ {i}, i ∈ S.params → i ≠ G := fun hi he =>
    hS.wf.notMem_gates_of_mem_params (he ▸ hi) hG
  have hKne : K ≠ G := fun h => hS.not_reads_self hG (h ▸ hKG)
  let env : Bool → Bool → ℕ → Bool := fun u v i =>
    if i = G then (S.gate G).op u v else if i = t₁ then u else if i = t₂ then v else false
  let g' : Gate := ⟨fun u v => (S.gate K).eval (env u v), .node t₁, .node t₂⟩
  have hg'reads : ∀ i, g'.Reads i → i = t₁ ∨ i = t₂ := by
    rintro i (h | h)
    · exact Or.inl (Arg.node.inj h).symm
    · exact Or.inr (Arg.node.inj h).symm
  have hok : S.RewireOK K g' := by
    refine ⟨hK, fun i hi => (hg'reads i hi).elim (fun h => h ▸ hx) (fun h => h ▸ hy),
      fun val hothers => ?_⟩
    change (S.gate K).eval (env (val t₁) (val t₂)) = (S.gate K).eval val
    obtain ⟨t, ht, hKt'⟩ : ∃ t, (t = t₁ ∨ t = t₂) ∧ (S.gate K).Reads t := by
      rcases hKt with h | h
      · exact ⟨t₁, Or.inl rfl, h⟩
      · exact ⟨t₂, Or.inr rfl, h⟩
    have htG : t ≠ G := by rcases ht with rfl | rfl; exacts [hGp hx, hGp hy]
    refine Gate.eval_congr fun i hi => ?_
    rcases Gate.eq_or_eq_of_reads htG.symm hKG hKt' hi with rfl | rfl
    · simp only [env, ite_true]
      rw [hothers G hG hKne.symm, Gate.eval_of_args hl hr]
    · rcases ht with rfl | rfl
      · simp only [env, ite_eq_right htG, ite_true]
      · simp only [env, ite_eq_right htG, ite_eq_right ht12.symm, ite_true]
  refine ⟨S.rewire K g', hS.preparation_rewire hok fun t ht _ => by
    rcases hg'reads t ht with rfl | rfl; exacts [hxdeg, hydeg], rfl, ?_, ?_⟩
  · rw [auxIn_eq (S := S.rewire K g') hne, auxIn_eq hne]
    change (S.rewire K g').auxArgs ((S.rewire K g').gate G) = S.auxArgs (S.gate G)
    rw [show (S.rewire K g').gate G = S.gate G from Function.update_of_ne hKne.symm _ _]
    rfl
  · have hgate : ∀ K', K' ≠ K → (S.rewire K g').gate K' = S.gate K' := fun K' h =>
      Function.update_of_ne h _ _
    have hgateK : (S.rewire K g').gate K = g' := Function.update_self _ _ _
    have hnot : ¬ g'.Reads G := fun hG' => by
      rcases hg'reads G hG' with h | h
      · exact hGp hx h.symm
      · exact hGp hy h.symm
    rw [childIn_eq (S := S.rewire K g') hne, childIn_eq hne]
    change (S.gates.filter fun K' => ((S.rewire K g').gate K').Reads G ∧
      ∃ t ∈ S.params, ((S.rewire K g').gate G).Reads t ∧ ((S.rewire K g').gate K').Reads t).card <
        (S.gates.filter fun K' => (S.gate K').Reads G ∧
          ∃ t ∈ S.params, (S.gate G).Reads t ∧ (S.gate K').Reads t).card
    refine Finset.card_lt_card ⟨fun K' hK' => ?_, fun hsub => ?_⟩
    · obtain ⟨hK'g, hK'G, t, htp, hGt, hK't⟩ := Finset.mem_filter.1 hK'
      have hK'K : K' ≠ K := by
        rintro rfl
        rw [hgateK] at hK'G
        exact hnot hK'G
      rw [hgate K' hK'K] at hK'G hK't
      rw [hgate G hKne.symm] at hGt
      exact Finset.mem_filter.2 ⟨hK'g, hK'G, t, htp, hGt, hK't⟩
    · have hKmem : K ∈ S.gates.filter fun K' => (S.gate K').Reads G ∧
          ∃ t ∈ S.params, (S.gate G).Reads t ∧ (S.gate K').Reads t := by
        refine Finset.mem_filter.2 ⟨hK, hKG, ?_⟩
        rcases hKt with h | h
        · exact ⟨t₁, hx, Or.inl hl, h⟩
        · exact ⟨t₂, hy, Or.inr hr, h⟩
      obtain ⟨-, hKG', -⟩ := Finset.mem_filter.1 (hsub hKmem)
      rw [hgateK] at hKG'
      exact hnot hKG'

/-! ### Eliminating the minimal AND -/

/-- The configuration of Section 4.3: `G` is an AND-type gate reading the distinct unpaired
parameters `x` and `y` with `2 ≤ deg y ≤ deg x`, no child of `G` reads `x` or `y`, and `G` is not
the output and has a child. -/
structure MinimalAnd (S : State n) (G x y : ℕ) : Prop where
  /-- `G` is a gate. -/
  mem : G ∈ S.gates
  /-- `G` is AND-type. -/
  and_op : ¬ IsAffineOp (S.gate G).op
  /-- `G` reads `x` and `y`. -/
  args : ((S.gate G).left = .node x ∧ (S.gate G).right = .node y) ∨
    ((S.gate G).left = .node y ∧ (S.gate G).right = .node x)
  /-- `x` is unpaired. -/
  unpaired_x : x ∈ S.unpaired
  /-- `y` is unpaired. -/
  unpaired_y : y ∈ S.unpaired
  /-- `x` and `y` are distinct. -/
  ne : x ≠ y
  /-- `y` has degree at least two. -/
  deg_y : 2 ≤ S.deg y
  /-- `x` has degree at least that of `y`. -/
  deg_le : S.deg y ≤ S.deg x
  /-- No child of `G` reads `x` or `y`. -/
  children : ∀ K ∈ S.gates, (S.gate K).Reads G → ¬ (S.gate K).Reads x ∧ ¬ (S.gate K).Reads y
  /-- `G` is not the output. -/
  not_out : ¬ S.out.Reads G
  /-- `G` has a child. -/
  has_child : ∃ K ∈ S.gates, (S.gate K).Reads G

namespace MinimalAnd

variable {S : State n} {G x y : ℕ}

/-- The first input `x` of a minimal AND is a parameter of `S`. -/
theorem mem_params_x (h : S.MinimalAnd G x y) : x ∈ S.params := (mem_unpaired.1 h.unpaired_x).1

/-- The second input `y` of a minimal AND is a parameter of `S`. -/
theorem mem_params_y (h : S.MinimalAnd G x y) : y ∈ S.params := (mem_unpaired.1 h.unpaired_y).1

/-- The minimal AND gate `G` is a child of its first input `x`. -/
theorem mem_children_x (h : S.MinimalAnd G x y) : Sum.inl G ∈ S.children x :=
  (SemiCircuit.inl_mem_children _).2 ⟨h.mem, (Gate.reads_of_args h.args).1⟩

/-- The minimal AND gate `G` is a child of its second input `y`. -/
theorem mem_children_y (h : S.MinimalAnd G x y) : Sum.inl G ∈ S.children y :=
  (SemiCircuit.inl_mem_children _).2 ⟨h.mem, (Gate.reads_of_args h.args).2⟩

/-- The minimal AND computes an AND-type operation of its inputs. -/
theorem exists_op (h : S.MinimalAnd G x y) : ∃ φ : Bool → Bool → Bool, ¬ IsAffineOp φ ∧
    ∀ val : ℕ → Bool, (S.gate G).eval val = φ (val x) (val y) := by
  obtain ⟨φ, hφ, hG⟩ := Gate.exists_op_of_args h.args
  exact ⟨φ, fun h' => h.and_op (hφ.1 h'), hG⟩

/-- No parameter of a valid state is equal to its minimal AND gate `G`. -/
theorem ne_gate (hS : S.Valid f) (h : S.MinimalAnd G x y) {u : ℕ} (hu : u ∈ S.params) : u ≠ G :=
  fun he => hS.wf.notMem_gates_of_mem_params hu (he ▸ h.mem)

/-- The children of `G` are gates. -/
theorem eq_inl_of_mem_children (hS : S.Valid f) (h : S.MinimalAnd G x y) {N : ℕ ⊕ ℕ}
    (hN : N ∈ S.children G) : ∃ K ∈ S.gates, N = .inl K ∧ (S.gate K).Reads G := by
  rcases N with K | e
  · obtain ⟨hK, hKG⟩ := (SemiCircuit.inl_mem_children _).1 hN
    exact ⟨K, hK, rfl, hKG⟩
  · obtain ⟨he, hGe⟩ := (SemiCircuit.inr_mem_children _).1 hN
    exact absurd hGe (hS.wf.notMem_terms_of_mem_gates h.mem he)

end MinimalAnd

/-- In a normal state with `d < a`, an AND-type gate `G` reading two parameters, no child of which
reads them, is a minimal AND in the sense of Section 4.3, its inputs ordered by degree: by
Lemma 2.3, `G` is not the output, and it has a child since no deletion applies. -/
theorem Valid.exists_minimalAnd {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G t₁ t₂ : ℕ} (hG : G ∈ S.gates)
    (hand : ¬ IsAffineOp (S.gate G).op) (hl : (S.gate G).left = .node t₁)
    (hr : (S.gate G).right = .node t₂) (ht12 : t₁ ≠ t₂) (hx : t₁ ∈ S.params) (hy : t₂ ∈ S.params)
    (hch : ∀ K ∈ S.gates, (S.gate K).Reads G → ¬ (S.gate K).Reads t₁ ∧ ¬ (S.gate K).Reads t₂) :
    ∃ x y, S.MinimalAnd G x y := by
  obtain ⟨hxu, hxdeg⟩ := hN.and_param G hG hand t₁ t₂ (Or.inl ⟨hl, hr⟩) hx hy ht12
  obtain ⟨hyu, hydeg⟩ := hN.and_param G hG hand t₂ t₁ (Or.inr ⟨hl, hr⟩) hy hx ht12.symm
  have hGout : ¬ S.out.Reads G := by
    intro hout
    obtain ⟨α, β, γ, hform⟩ := exists_and_form hand
    refine hS.false_of_fix hf ha hy β ∅ (Finset.empty_subset _) (Finset.notMem_empty _)
      (γ ^^ S.out.neg) fun val hval hfix => ?_
    rw [Finset.sum_empty, add_zero] at hfix
    unfold Lit.eval
    unfold Lit.Reads at hout
    rw [hout, Arg.eval_node, hval.2 G hG, Gate.eval_of_args hl hr, hform, hfix]
    cases val t₁ <;> cases α <;> cases β <;> cases γ <;> cases S.out.neg <;> rfl
  have hhas : ∃ K ∈ S.gates, (S.gate K).Reads G := by
    by_contra hno
    push Not at hno
    exact hN.no_deletion (Or.inr (Or.inr (Or.inl ⟨G, hG, hno, hGout⟩)))
  by_cases hle : S.deg t₂ ≤ S.deg t₁
  · exact ⟨t₁, t₂, hG, hand, Or.inl ⟨hl, hr⟩, hxu, hyu, ht12, hydeg, hle, hch, hGout, hhas⟩
  · exact ⟨t₂, t₁, hG, hand, Or.inr ⟨hl, hr⟩, hyu, hxu, ht12.symm, hxdeg, by omega,
      fun K hK hKG => (hch K hK hKG).symm, hGout, hhas⟩

end State

end Cslib.Circuits.Boolean.AffineDisperser
