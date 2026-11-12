/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.NNF.Basic
public import CslibFrontier.Computability.Communication.MultiPartition

/-!
# DNNF size bounds the multi-partition cover number

**Theorem** [BovaCapelliMengelSlivovsky2016]
[ArenasBroadrickLiewVanDenBroeck2026, Theorem 3.1]. If a DNNF with `s` nodes computes
`f : (ι → Bool) → Bool` and there are at least two variables, then `f⁻¹(1)` is the union of at
most `s` balanced rectangles: `Cov^m_1(f) ≤ s` (`NNF.coverNumberFun_le_size`). Applied to a
DNNF for `¬f`, this bounds `Cov^m_0(f)` by the DNNF size of `¬f`
(`NNF.coverNumberFun_false_le_size`).

**Certificates.** A node *occurs* for an accepted input `x` (`NNF.Occurs`) when it is the output,
a child of an occurring `∧` gate, or a child of an occurring `∨` gate that accepts `x`. If a node
`v` occurs for `y`, then every input that `v` accepts and that agrees with `y` outside the
variables of `v` is accepted (`NNF.Occurs.toFun_eq_true`): decomposability keeps the siblings
along the way independent of the replaced variables. This is the unsmoothed analogue of
`DecomposableDAG.Occurs.mem_accepted` for smooth decomposable DAGs
(`CslibFrontier/Computability/Circuit/Decomposable.lean`); that model requires smoothness, which can
cost more than a constant factor in size, so it is not reused here.

**One rectangle per node.** Let `n = |ι|`. A node whose variable set `X` is balanced contributes
the inputs it accepts whose part outside `X` comes from an input for which it occurs: a rectangle
for `X`. Walking down from the output along the certificate of an accepted input, always to the
child with more variables at an `∧` gate and to an accepting child at an `∨` gate, the variable
count halves at most at `∧` gates; so the walk meets a balanced node, unless an `∨` gate `u` with
more than `2n/3` variables has an accepting child `c` with fewer than `n/3`. Then the inputs
accepted by `c` whose part outside a balanced `X`, with `vars c ⊆ X ⊆ vars u`, comes from an
occurrence of `u` form a rectangle charged to `u`. At most one child of `u` is that small, and `u`
is not balanced, so every node is charged at most once. If the output itself has fewer than `n/3`
variables, `f⁻¹(1)` is a single rectangle.

The model allows constant leaves and counts every node, so the bound is in the paper's form.

## Main definitions

* `Cslib.Circuits.NNF.Occurs`: nodes on the certificate of an accepted input.

## Main results

* `Cslib.Circuits.NNF.Occurs.toFun_eq_true`: substitution below an occurring node.
* `Cslib.Circuits.NNF.exists_isCover`: a DNNF with `s` nodes gives a cover of `f⁻¹(1)` by `s`
  balanced rectangles.
* `Cslib.Circuits.NNF.coverNumberFun_le_size`, `Cslib.Circuits.NNF.coverNumberFun_false_le_size`:
  `Cov^m_1(f)` and `Cov^m_0(f)` are at most the size of a DNNF for `f` and for `¬f`.

## References

* [S. Bova, F. Capelli, S. Mengel, F. Slivovsky, *Knowledge compilation meets communication
  complexity*][BovaCapelliMengelSlivovsky2016]
* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib.Circuits.NNF

open Set Cslib.Communication.MultiPartition

variable {ι N : Type*} [DecidableEq ι] {C : NNF ι N}

variable (C) in
/-- A node *occurs* on the accepting certificate of the input `x`. -/
inductive Occurs (x : ι → Bool) : N → Prop
  /-- The output occurs when it accepts `x`. -/
  | root : C.toFun x = true → Occurs x C.root
  /-- The left child of an occurring `∧` gate occurs. -/
  | andLeft {v l r : N} : Occurs x v → C.gate v = .and l r → Occurs x l
  /-- The right child of an occurring `∧` gate occurs. -/
  | andRight {v l r : N} : Occurs x v → C.gate v = .and l r → Occurs x r
  /-- A child of an occurring `∨` gate that accepts `x` occurs. -/
  | orChild {v l r c : N} : Occurs x v → C.gate v = .or l r → (c = l ∨ c = r) →
      C.eval x c = true → Occurs x c

omit [DecidableEq ι] in
/-- A node occurring for `x` accepts `x`. -/
theorem Occurs.eval_eq_true {x : ι → Bool} {v : N} (h : C.Occurs x v) :
    C.eval x v = true := by
  induction h with
  | root h => exact h
  | andLeft _ hg ih => rw [eval_and hg] at ih; exact (Bool.and_eq_true _ _ ▸ ih).1
  | andRight _ hg ih => rw [eval_and hg] at ih; exact (Bool.and_eq_true _ _ ▸ ih).2
  | orChild _ _ _ h => exact h

/-- **Substitution.** If the node `v` occurs for `y` in a DNNF, then every input accepted by `v`
that agrees with `y` outside the variables of `v` is accepted. -/
theorem Occurs.toFun_eq_true (hC : C.IsDecomposable) {y : ι → Bool} {v : N}
    (h : C.Occurs y v) {z : ι → Bool} (hz : C.eval z v = true)
    (hout : ∀ i ∉ C.vars v, z i = y i) : C.toFun z = true := by
  induction h with
  | root _ => exact hz
  | @andLeft v l r hv hg ih =>
    have hr : C.eval z r = C.eval y r := C.eval_congr r fun i hi =>
      hout i fun hil => Finset.disjoint_left.mp (hC v l r hg) hil hi
    have hyr : C.eval y r = true := by
      have := hv.eval_eq_true; rw [eval_and hg] at this; exact (Bool.and_eq_true _ _ ▸ this).2
    exact ih (by rw [eval_and hg, hz, hr, hyr]; rfl) fun i hi =>
      hout i fun hil => hi (by rw [vars_and hg]; exact Finset.mem_union_left _ hil)
  | @andRight v l r hv hg ih =>
    have hl : C.eval z l = C.eval y l := C.eval_congr l fun i hi =>
      hout i fun hir => Finset.disjoint_left.mp (hC v l r hg) hi hir
    have hyl : C.eval y l = true := by
      have := hv.eval_eq_true; rw [eval_and hg] at this; exact (Bool.and_eq_true _ _ ▸ this).1
    exact ih (by rw [eval_and hg, hz, hl, hyl]; rfl) fun i hi =>
      hout i fun hir => hi (by rw [vars_and hg]; exact Finset.mem_union_right _ hir)
  | @orChild v l r c _ hg hc _ ih =>
    have hsub : C.vars c ⊆ C.vars v := by
      rw [vars_or hg]
      rcases hc with rfl | rfl
      exacts [Finset.subset_union_left, Finset.subset_union_right]
    refine ih ?_ fun i hi => hout i fun hic => hi (hsub hic)
    rw [eval_or hg]
    rcases hc with rfl | rfl <;> simp [hz]

/-! ### One rectangle per node -/

variable [Fintype ι]

/-- The inputs accepted by `c` whose part outside `X` comes from an input for which `v` occurs. -/
private def certRect (C : NNF ι N) (v c : N) (X : Finset ι) : Set (ι → Bool) :=
  {z | C.eval z c = true ∧ ∃ y, C.Occurs y v ∧ ∀ i ∉ X, z i = y i}

omit [Fintype ι] in
private theorem piecewise_mem_certRect {v c : N} {X : Finset ι} (hcX : C.vars c ⊆ X)
    {x z : ι → Bool} (hx : x ∈ certRect C v c X) (hz : z ∈ certRect C v c X) :
    X.piecewise x z ∈ certRect C v c X := by
  obtain ⟨hxc, -⟩ := hx
  obtain ⟨-, y, hy, hzy⟩ := hz
  refine ⟨?_, y, hy, fun i hi => ?_⟩
  · rw [C.eval_congr c fun i hi => Finset.piecewise_eq_of_mem _ _ _ (hcX hi)]
    exact hxc
  · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]
    exact hzy i hi

omit [Fintype ι] in
private theorem certRect_subset (hC : C.IsDecomposable) {v c : N} {X : Finset ι}
    (hXv : X ⊆ C.vars v) (hcv : ∀ z, C.eval z c = true → C.eval z v = true) :
    certRect C v c X ⊆ C.toFun ⁻¹' {true} := by
  rintro z ⟨hzc, y, hy, hzy⟩
  exact hy.toFun_eq_true hC (hcv z hzc) fun i hi => hzy i fun hiX => hi (hXv hiX)

open Classical in
/-- The rectangle charged to a node, as described in the module docstring. -/
private noncomputable def nodeRect (C : NNF ι N) (v : N) : Set (ι → Bool) :=
  if IsBalanced (C.vars v) then certRect C v v (C.vars v)
  else
    match C.gate v with
    | .or l r =>
      if 3 * (C.vars l).card < Fintype.card ι then
        if h : ∃ X, C.vars l ⊆ X ∧ X ⊆ C.vars v ∧ IsBalanced X then certRect C v l h.choose else ∅
      else if 3 * (C.vars r).card < Fintype.card ι then
        if h : ∃ X, C.vars r ⊆ X ∧ X ⊆ C.vars v ∧ IsBalanced X then certRect C v r h.choose else ∅
      else ∅
    | _ => ∅

private theorem isBalancedRectangle_nodeRect (hn : 2 ≤ Fintype.card ι) (v : N) :
    IsBalancedRectangle (nodeRect C v) := by
  obtain ⟨X₀, -, -, hX₀⟩ := exists_isBalanced hn (Finset.empty_subset Finset.univ)
    (by simp) (by simp; omega)
  unfold nodeRect
  split_ifs with hv
  · exact isBalancedRectangle_of_piecewise_mem hv fun _ hx _ hz =>
      piecewise_mem_certRect subset_rfl hx hz
  · split
    · split_ifs with _ h _ h
      · exact isBalancedRectangle_of_piecewise_mem h.choose_spec.2.2 fun _ hx _ hz =>
          piecewise_mem_certRect h.choose_spec.1 hx hz
      · exact isBalancedRectangle_empty hX₀
      · exact isBalancedRectangle_of_piecewise_mem h.choose_spec.2.2 fun _ hx _ hz =>
          piecewise_mem_certRect h.choose_spec.1 hx hz
      · exact isBalancedRectangle_empty hX₀
      · exact isBalancedRectangle_empty hX₀
    all_goals exact isBalancedRectangle_empty hX₀

private theorem nodeRect_subset (hC : C.IsDecomposable) (v : N) :
    nodeRect C v ⊆ C.toFun ⁻¹' {true} := by
  unfold nodeRect
  split_ifs
  · exact certRect_subset hC subset_rfl fun _ h => h
  · split
    next l r hg =>
      split_ifs with _ h _ h
      · exact certRect_subset hC h.choose_spec.2.1 fun z hz => by simp [eval_or hg, hz]
      · exact empty_subset _
      · exact certRect_subset hC h.choose_spec.2.1 fun z hz => by simp [eval_or hg, hz]
      · exact empty_subset _
      · exact empty_subset _
    all_goals exact empty_subset _

private theorem isBalanced_iff {X : Finset ι} :
    IsBalanced X ↔ Fintype.card ι ≤ 3 * X.card ∧ 3 * X.card ≤ 2 * Fintype.card ι := by
  have := X.card_le_univ
  simp only [IsBalanced, Finset.card_compl]
  omega

/-- **The descent.** An input for which a node with more than `2n/3` variables occurs lies in
the rectangle of some node. -/
private theorem exists_mem_nodeRect (hn : 2 ≤ Fintype.card ι) {x : ι → Bool} :
    ∀ u : N, C.Occurs x u → 2 * Fintype.card ι < 3 * (C.vars u).card →
      ∃ v : N, x ∈ nodeRect C v := by
  set n := Fintype.card ι
  -- A balanced occurring node contains the input in its own rectangle.
  have hown : ∀ v, C.Occurs x v → IsBalanced (C.vars v) → x ∈ nodeRect C v := fun v hv hb => by
    unfold nodeRect
    rw [ite_eq_left hb]
    exact ⟨hv.eval_eq_true, x, hv, fun _ _ => rfl⟩
  intro u
  induction u using induction_on with
  | h u ih =>
    intro hu hlarge
    cases hg : C.gate u with
    | lit i b => have := C.card_vars_le_one_of_not_gate (v := u) (by simp [hg]); omega
    | const b => have := C.card_vars_le_one_of_not_gate (v := u) (by simp [hg]); omega
    | and l r =>
      have hlt := C.and_lt u l r hg
      have hcard : (C.vars u).card ≤ (C.vars l).card + (C.vars r).card := by
        rw [vars_and hg]; exact Finset.card_union_le _ _
      -- Go to the child with more variables.
      have step : ∀ c, C.rank c < C.rank u → C.Occurs x c → (C.vars u).card ≤ 2 * (C.vars c).card →
          ∃ v, x ∈ nodeRect C v := fun c hc hxc h2 => by
        by_cases hbig : 2 * n < 3 * (C.vars c).card
        · exact ih c hc hxc hbig
        · exact ⟨c, hown c hxc (isBalanced_iff.mpr ⟨by omega, by omega⟩)⟩
      by_cases hlr : (C.vars r).card ≤ (C.vars l).card
      · exact step l hlt.1 (.andLeft hu hg) (by omega)
      · exact step r hlt.2 (.andRight hu hg) (by omega)
    | or l r =>
      have hlt := C.or_lt u l r hg
      have hcard : (C.vars u).card ≤ (C.vars l).card + (C.vars r).card := by
        rw [vars_or hg]; exact Finset.card_union_le _ _
      have hnb : ¬IsBalanced (C.vars u) := fun h => by have := isBalanced_iff.mp h; omega
      have hxu := hu.eval_eq_true
      rw [eval_or hg, Bool.or_eq_true] at hxu
      -- Small accepting children are charged to `u`.
      have hsmall : ∀ c, (c = l ∨ c = r) → C.eval x c = true → 3 * (C.vars c).card < n →
          x ∈ nodeRect C u := fun c hc hxc hcs => by
        unfold nodeRect
        rw [ite_eq_right hnb]
        simp only [hg]
        rcases hc with rfl | rfl
        · rw [ite_eq_left hcs, dite_eq_left (exists_isBalanced hn
            (by rw [vars_or hg]; exact Finset.subset_union_left) (by omega) (by omega))]
          exact ⟨hxc, x, hu, fun _ _ => rfl⟩
        · rw [ite_eq_right (by omega), ite_eq_left hcs, dite_eq_left (exists_isBalanced hn
            (by rw [vars_or hg]; exact Finset.subset_union_right) (by omega) (by omega))]
          exact ⟨hxc, x, hu, fun _ _ => rfl⟩
      have step : ∀ c, C.rank c < C.rank u → (c = l ∨ c = r) → C.eval x c = true →
          ∃ v, x ∈ nodeRect C v :=
        fun c hc hcl hxc => by
          have hxo : C.Occurs x c := .orChild hu hg hcl hxc
          by_cases hbig : 2 * n < 3 * (C.vars c).card
          · exact ih c hc hxo hbig
          by_cases hlow : 3 * (C.vars c).card < n
          · exact ⟨u, hsmall c hcl hxc hlow⟩
          · exact ⟨c, hown c hxo (isBalanced_iff.mpr ⟨by omega, by omega⟩)⟩
      rcases hxu with h | h
      · exact step l hlt.1 (.inl rfl) h
      · exact step r hlt.2 (.inr rfl) h

/-- One balanced rectangle per node covers the inputs accepted by a DNNF. -/
private theorem exists_nodeCover (hC : C.IsDecomposable) (hn : 2 ≤ Fintype.card ι) :
    ∃ R : N → Set (ι → Bool), (∀ v, IsBalancedRectangle (R v)) ∧
      ⋃ v, R v = C.toFun ⁻¹' {true} := by
  classical
  set n := Fintype.card ι
  by_cases hroot : 3 * (C.vars C.root).card < n
  · -- The output has few variables: its accepted set is a single rectangle.
    obtain ⟨X, hX, -, hXb⟩ := exists_isBalanced hn (Finset.subset_univ (C.vars C.root))
      (by omega) (by simp; omega)
    refine ⟨fun v => if v = C.root then C.toFun ⁻¹' {true} else ∅, fun v => ?_, ?_⟩
    · dsimp only
      split_ifs
      · refine isBalancedRectangle_of_piecewise_mem hXb fun x hx z _ => ?_
        simp only [mem_preimage, mem_singleton_iff, toFun] at hx ⊢
        rw [C.eval_congr C.root fun i hi => Finset.piecewise_eq_of_mem _ _ _ (hX hi)]
        exact hx
      · exact isBalancedRectangle_empty hXb
    · refine subset_antisymm (iUnion_subset fun v => ?_) fun x hx =>
        mem_iUnion.mpr ⟨C.root, by simpa using hx⟩
      split_ifs
      exacts [subset_rfl, empty_subset _]
  · refine ⟨nodeRect C, isBalancedRectangle_nodeRect hn, subset_antisymm
      (iUnion_subset (nodeRect_subset hC)) fun x hx => mem_iUnion.mpr ?_⟩
    have hxr : C.Occurs x C.root := .root hx
    by_cases hbig : 2 * n < 3 * (C.vars C.root).card
    · exact exists_mem_nodeRect hn C.root hxr hbig
    · refine ⟨C.root, ?_⟩
      unfold nodeRect
      rw [ite_eq_left (isBalanced_iff.mpr ⟨by omega, by omega⟩)]
      exact ⟨hxr.eval_eq_true, x, hxr, fun _ _ => rfl⟩

/-- **DNNF size bounds the cover number**, in the form of an explicit cover: a DNNF with `s`
nodes over at least two variables gives a cover of the inputs it accepts by `s` balanced
rectangles. -/
theorem exists_isCover [Fintype N] (hC : C.IsDecomposable) (hn : 2 ≤ Fintype.card ι) :
    ∃ R : Fin C.size → Set (ι → Bool), IsCover (C.toFun ⁻¹' {true}) R := by
  obtain ⟨R, hR, hU⟩ := exists_nodeCover hC hn
  refine ⟨fun i => R ((Fintype.equivFin N).symm i), fun i => hR _, ?_⟩
  rw [← hU]
  exact (Fintype.equivFin N).symm.iSup_comp (g := R)

/-- **[BovaCapelliMengelSlivovsky2016], [ArenasBroadrickLiewVanDenBroeck2026, Theorem 3.1].**
Every DNNF computing `f` over at least two variables has at least `Cov^m_1(f)` nodes. -/
theorem coverNumberFun_le_size [Fintype N] (hC : C.IsDecomposable) (hn : 2 ≤ Fintype.card ι) :
    coverNumberFun true C.toFun ≤ C.size := by
  obtain ⟨R, hR⟩ := exists_isCover hC hn
  exact hR.coverNumber_le

/-- Every DNNF computing `¬f` over at least two variables has at least `Cov^m_0(f)` nodes. -/
theorem coverNumberFun_false_le_size [Fintype N] (hC : C.IsDecomposable) (hn : 2 ≤ Fintype.card ι)
    {f : (ι → Bool) → Bool} (hf : ∀ x, C.toFun x = !f x) :
    coverNumberFun false f ≤ C.size := by
  have : f ⁻¹' {false} = C.toFun ⁻¹' {true} := by ext x; simp [hf]
  rw [coverNumberFun, this]
  exact coverNumberFun_le_size hC hn

end Cslib.Circuits.NNF
