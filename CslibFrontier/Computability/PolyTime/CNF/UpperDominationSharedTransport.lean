/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedQueries
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Basic
import all CslibFrontier.Computability.PolyTime.CNF.WeightedPlan

/-!
# Count transport for the global shared-marker queries

## Main definitions

* `project`, `extend`: forget the new suffix markers or compute them from the old ports.
* `modelEquiv`: the actual boundary-model bijection on a canonical graph.

## Main results

* `query_forced_markers`: the refined query is the old query with forced marker values.
* `query_count_eq`: equality of each boundary count, including unused declared bits.
* `compile_count`: exact original-set count, including the empty graph and signed threshold.

Projection forgets exactly the suffix markers of [ChenJiangZhu2027], Appendix D.3 (PDF p.35).
The inverse sets each marker to the parity of its two old ports, substituting the final boundary.
All predicates retain the same original assignment, including overlapping selection/mark wires.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

open WeightedRow

/-- Split the actual old query at the source's prefix/suffix boundary. -/
private theorem old_query_split (x : UpperDomination.Input) (β : Bool) :
    TwoBoundary.BinaryFrontend.query (Unique.build x) β =
      TwoBoundary.BinaryFrontend.side (UpperDomination.build x) ++ prefixClauses x β ++
        (List.range (IndependentDomination.order (graph x))).flatMap fun w =>
          ((complete (coreInput x)).getD w []).flatMap
            (BinaryQuery.termClauses (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
              ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
              ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w)) := by
  let P := TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)
  let Q := complete (coreInput x)
  have hQ : Q.length = IndependentDomination.order (graph x) := by
    simp [Q, complete, coreInput, coreGraph]
  change _ ++ (List.range (P ++ Q).length).flatMap _ = _
  simp only [List.length_append, List.range_add, List.flatMap_append, List.flatMap_map]
  rw [← List.append_assoc]
  congr 1
  · congr 1
    apply List.flatMap_congr
    intro j hj
    have hj' : (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).getD j [] =
        P.getD j [] := List.getD_append P Q [] j (List.mem_range.mp hj)
    rw [hj']
    rfl
  · rw [hQ]
    apply List.flatMap_congr
    intro w _
    have hw' : (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).getD (P.length + w) [] =
        Q.getD (P.length + w - P.length) [] :=
      List.getD_append_right P Q [] (P.length + w) (by omega)
    rw [hw']
    simp only [Nat.add_sub_cancel_left]
    rfl

private theorem suffix_eval (x : UpperDomination.Input) (β : Bool) (σ : ℕ → Bool) (w : ℕ)
    (hw : w < IndependentDomination.order (graph x)) :
    CNF.eval σ (((complete (coreInput x)).getD w []).flatMap
      (BinaryQuery.termClauses (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
        ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
        ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w))) = true ↔
      (DNF.eval σ (context x β w).terms = true →
        (σ (context x β w).left ^^
          (if (context x β w).last then β else σ (context x β w).right)) = false) := by
  obtain ⟨_, hp, hfull⟩ := layout x
  have hj : (TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w ≠ 0 :=
    by omega
  have he : (TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w =
      (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1 ↔
        w + 1 = IndependentDomination.order (graph x) := by omega
  have ht (t : Term ℕ) :
      CNF.eval σ (BinaryQuery.termClauses
        (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
        ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
        ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w) t) = true ↔
      (Term.eval σ t = true →
        (σ (context x β w).left ^^
          (if (context x β w).last then β else σ (context x β w).right)) = false) := by
    have hneg : Clause.eval σ (t.map fun l => (l.1, !l.2)) = !Term.eval σ t :=
      Term.eval_negate σ t
    simp only [BinaryQuery.termClauses, hj, ↓reduceIte, he]
    by_cases hl : w + 1 = IndependentDomination.order (graph x)
    all_goals
      simp only [hl, ↓reduceIte, CNF.eval, List.all_cons, List.all_nil, Bool.and_true,
        Clause.eval, List.any_append]
      simp only [Clause.eval] at hneg
      rw [hneg]
      cases ha : σ (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) +
        ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w) - 1) <;>
        cases hb : σ (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) +
          ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w)) <;>
          cases β <;> cases hv : Term.eval σ t <;>
            simp [context, hl, Literal.eval, ha, hb]
  have hall : CNF.eval σ (((complete (coreInput x)).getD w []).flatMap
      (BinaryQuery.termClauses (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
        ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
        ((TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length + w))) = true ↔
      ∀ t ∈ (complete (coreInput x)).getD w [],
        CNF.eval σ (BinaryQuery.termClauses
          (TwoBoundary.BinaryFrontend.declared (UpperDomination.build x))
          ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β
          ((TwoBoundary.BinaryFrontend.conditions
          (UpperDomination.build x)).length + w) t) = true := by
    simp only [CNF.eval, List.all_flatMap, List.all_eq_true]
  rw [hall]
  simp_rw [ht]
  simp only [context, DNF.eval_eq_true_iff]
  aesop

private theorem old_query_eval (x : UpperDomination.Input) (β : Bool) (σ : ℕ → Bool) :
    (TwoBoundary.BinaryFrontend.query (Unique.build x) β).eval σ = true ↔
      (TwoBoundary.BinaryFrontend.side (UpperDomination.build x)).eval σ = true ∧
        (prefixClauses x β).eval σ = true ∧
        ∀ w < IndependentDomination.order (graph x),
          DNF.eval σ (context x β w).terms = true →
            (σ (context x β w).left ^^
              (if (context x β w).last then β else σ (context x β w).right)) = false := by
  rw [old_query_split, CNF.eval_append, CNF.eval_append, Bool.and_eq_true, Bool.and_eq_true,
    and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  simp only [CNF.eval, List.all_flatMap, List.all_eq_true, List.mem_range]
  apply forall_congr'
  intro w
  apply imp_congr_right
  intro hw
  simpa only [CNF.eval, List.all_flatMap, List.all_eq_true] using suffix_eval x β σ w hw

/-- The whole refined formula is the old formula together with the uniquely forced marker bits.
This identity concerns actual assembled lists, not an assumed query-count contract. -/
theorem query_forced_markers (x : UpperDomination.Input) (β : Bool) (σ : ℕ → Bool) :
    (query x β).eval σ = true ↔
      (TwoBoundary.BinaryFrontend.query (Unique.build x) β).eval σ = true ∧
        ∀ w < IndependentDomination.order (graph x),
          σ (oldDeclaration x + w) =
            (σ (context x β w).left ^^
              (if (context x β w).last then β else σ (context x β w).right)) := by
  rw [query_eval, old_query_eval]
  constructor
  · rintro ⟨hs, hp, hm⟩
    refine ⟨⟨hs, hp, ?_⟩, fun w hw => (hm w hw).1⟩
    intro w hw ht
    rw [← (hm w hw).1]
    exact (hm w hw).2 ht
  · rintro ⟨⟨hs, hp, ht⟩, hm⟩
    refine ⟨hs, hp, fun w hw => ⟨hm w hw, ?_⟩⟩
    intro hterm
    change σ (oldDeclaration x + w) = false
    rw [hm w hw]
    exact ht w hw hterm

/-- Forget the suffix markers, retaining every old declared variable (including unused bits). -/
@[expose] def project (x : UpperDomination.Input)
    (τ : Fin (oldDeclaration x + IndependentDomination.order (graph x)) → Bool) :
    Fin (oldDeclaration x) → Bool :=
  fun i => τ ⟨i.val, i.isLt.trans_le (Nat.le_add_right _ _)⟩

/-- The executable inverse projection assigns marker `w` the parity of its old ports. -/
@[expose] def extend (x : UpperDomination.Input) (β : Bool)
    (σ : Fin (oldDeclaration x) → Bool) :
    Fin (oldDeclaration x + IndependentDomination.order (graph x)) → Bool :=
  fun i => if hi : i.val < oldDeclaration x then σ ⟨i.val, hi⟩ else
    let c := context x β (i.val - oldDeclaration x)
    BinaryPlan.assignment σ c.left ^^
      (if c.last then β else BinaryPlan.assignment σ c.right)

/-- Projection is a left inverse of the computed parity extension. -/
theorem project_extend (x : UpperDomination.Input) (β : Bool)
    (σ : Fin (oldDeclaration x) → Bool) : project x (extend x β σ) = σ := by
  funext i
  simp [project, extend, i.isLt]

private theorem assignment_project (x : UpperDomination.Input)
    (τ : Fin (oldDeclaration x + IndependentDomination.order (graph x)) → Bool)
    (i : ℕ) (hi : i < oldDeclaration x) :
    BinaryPlan.assignment τ i = BinaryPlan.assignment (project x τ) i := by
  simp [BinaryPlan.assignment, hi, hi.trans_le (Nat.le_add_right _ _), project]

private theorem old_query_congr (x : UpperDomination.Input) (β : Bool)
    (hv : ∀ c ∈ TwoBoundary.BinaryFrontend.query (Unique.build x) β,
      ∀ l ∈ c, l.1 < oldDeclaration x)
    (τ : Fin (oldDeclaration x + IndependentDomination.order (graph x)) → Bool) :
    (TwoBoundary.BinaryFrontend.query (Unique.build x) β).eval (BinaryPlan.assignment τ) =
      (TwoBoundary.BinaryFrontend.query (Unique.build x) β).eval
        (BinaryPlan.assignment (project x τ)) := by
  apply CNF.eval_congr
  intro i hi
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hi
  exact assignment_project x τ i (hv c hc (i, b) hl)

private theorem parity_project (x : UpperDomination.Input) (β : Bool)
    (τ : Fin (oldDeclaration x + IndependentDomination.order (graph x)) → Bool)
    (w : ℕ) (hw : w < IndependentDomination.order (graph x)) :
    (BinaryPlan.assignment τ (context x β w).left ^^
      (if (context x β w).last then β else BinaryPlan.assignment τ (context x β w).right)) =
    (BinaryPlan.assignment (project x τ) (context x β w).left ^^
      (if (context x β w).last then β else
        BinaryPlan.assignment (project x τ) (context x β w).right)) := by
  obtain ⟨hl, hr, _, _⟩ := context_ports x β w hw
  rw [assignment_project x τ _ hl]
  by_cases ht : (context x β w).last = true
  · simp only [ht, ↓reduceIte]
  · have hf : (context x β w).last = false := Bool.eq_false_iff.mpr ht
    simp only [hf, Bool.false_eq_true, ↓reduceIte, assignment_project x τ _ (hr hf)]

private theorem extend_marker (x : UpperDomination.Input) (β : Bool)
    (σ : Fin (oldDeclaration x) → Bool) (w : ℕ)
    (hw : w < IndependentDomination.order (graph x)) :
    BinaryPlan.assignment (extend x β σ) (oldDeclaration x + w) =
      (BinaryPlan.assignment σ (context x β w).left ^^
        (if (context x β w).last then β else BinaryPlan.assignment σ (context x β w).right)) := by
  have hi : oldDeclaration x + w <
      oldDeclaration x + IndependentDomination.order (graph x) := by omega
  have hn : ¬ oldDeclaration x + w < oldDeclaration x := by omega
  simp only [BinaryPlan.assignment, hi, ↓reduceDIte, extend, Nat.add_sub_cancel_left, hn]

open Classical in
private noncomputable def modelsEquiv (x : UpperDomination.Input) (β : Bool)
    (hv : ∀ c ∈ TwoBoundary.BinaryFrontend.query (Unique.build x) β,
      ∀ l ∈ c, l.1 < oldDeclaration x) :
    {τ : Fin (oldDeclaration x + IndependentDomination.order (graph x)) → Bool //
      (query x β).eval (BinaryPlan.assignment τ) = true} ≃
    {σ : Fin (oldDeclaration x) → Bool //
      (TwoBoundary.BinaryFrontend.query (Unique.build x) β).eval
        (BinaryPlan.assignment σ) = true} where
  toFun τ := ⟨project x τ.val, by
    rw [← old_query_congr x β hv τ.val]
    exact ((query_forced_markers x β _).mp τ.property).1⟩
  invFun σ := ⟨extend x β σ.val, by
    apply (query_forced_markers x β _).mpr
    refine ⟨?_, ?_⟩
    · rw [old_query_congr x β hv, project_extend]
      exact σ.property
    · intro w hw
      rw [parity_project x β _ w hw, project_extend]
      exact extend_marker x β σ.val w hw⟩
  left_inv τ := by
    apply Subtype.ext
    funext i
    change extend x β (project x τ.val) i = τ.val i
    by_cases hi : i.val < oldDeclaration x
    · simp [extend, hi, project]
    · have hw : i.val - oldDeclaration x < IndependentDomination.order (graph x) := by
        have := i.isLt
        omega
      have he : oldDeclaration x + (i.val - oldDeclaration x) = i.val := by omega
      have hm := ((query_forced_markers x β _).mp τ.property).2 _ hw
      rw [parity_project x β τ.val _ hw, he] at hm
      have hai : BinaryPlan.assignment τ.val i.val = τ.val i := by
        simp [BinaryPlan.assignment, i.isLt]
      rw [hai] at hm
      simpa only [extend, hi, ↓reduceDIte] using hm.symm
  right_inv σ := Subtype.ext (project_extend x β σ.val)

private theorem old_query_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    (oldDeclaration (ofGraph G k), TwoBoundary.BinaryFrontend.query
      (Unique.build (ofGraph G k)) β) ∈ TwoBoundary.BinaryFrontend.queries
        (TwoBoundary.BinaryFrontend.compile (Unique.build (ofGraph G k))) := by
  let x := ofGraph G k
  have hn' : 1 ≤ IndependentDomination.order (graph x) := hn
  have hp : (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    have hl := (layout x).2.2
    omega
  have hq : (oldDeclaration x, TwoBoundary.BinaryFrontend.query (Unique.build x) β) ∈
      TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile (Unique.build x)) := by
    cases β <;>
      simp [TwoBoundary.BinaryFrontend.compile, hp, TwoBoundary.BinaryFrontend.queries,
        oldDeclaration]
  exact hq

private theorem old_query_indices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    ∀ c ∈ TwoBoundary.BinaryFrontend.query (Unique.build (ofGraph G k)) β,
      ∀ l ∈ c, l.1 < oldDeclaration (ofGraph G k) := by
  exact fun c hc =>
    (Unique.query_budget G k hn _ _ (old_query_mem G k hn β)).2.2 c hc |>.2

open Classical in
/-- Projection/parity-extension bijection for each boundary of the actual graph query.
No supplied literal-bound or count-correctness premise is needed. -/
noncomputable def modelEquiv {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    {τ : Fin (oldDeclaration (ofGraph G k) + n) → Bool //
      (query (ofGraph G k) β).eval (BinaryPlan.assignment τ) = true} ≃
    {σ : Fin (oldDeclaration (ofGraph G k)) → Bool //
      (TwoBoundary.BinaryFrontend.query (Unique.build (ofGraph G k)) β).eval
        (BinaryPlan.assignment σ) = true} :=
  modelsEquiv (ofGraph G k) β (old_query_indices G k hn β)

open Classical in
/-- The model bijection's forward map is the actual projection of declared bits. -/
theorem modelEquiv_apply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool)
    (τ : {τ : Fin (oldDeclaration (ofGraph G k) + n) → Bool //
      (query (ofGraph G k) β).eval (BinaryPlan.assignment τ) = true}) :
    (modelEquiv G k hn β τ).val = project (ofGraph G k) τ.val := by rfl

open Classical in
/-- Its inverse computes the new marker bits by old-port parity, with no marker advice. -/
theorem modelEquiv_symm_apply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool)
    (σ : {σ : Fin (oldDeclaration (ofGraph G k)) → Bool //
      (TwoBoundary.BinaryFrontend.query (Unique.build (ofGraph G k)) β).eval
        (BinaryPlan.assignment σ) = true}) :
    ((modelEquiv G k hn β).symm σ).val = extend (ofGraph G k) β σ.val := by rfl

/-- Each actual refined boundary query has exactly the old model count. Projection and parity
extension in `modelsEquiv` retain every old declared bit, including unused original variables. -/
theorem query_count_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    BinaryPlan.queryCount (oldDeclaration (ofGraph G k) + n) (query (ofGraph G k) β) =
      BinaryPlan.queryCount (oldDeclaration (ofGraph G k))
        (TwoBoundary.BinaryFrontend.query (Unique.build (ofGraph G k)) β) := by
  classical
  exact Fintype.card_congr (modelEquiv G k hn β)

open Classical in
/-- The actual empty/two-query dispatch counts original minimal dominating sets, with no mark
multiplicity. Each boundary count is transported separately before the old difference identity. -/
theorem compile_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ) :
    TwoBoundary.BinaryFrontend.value (compile (ofGraph G k)) =
      Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
  classical
  obtain ⟨B, P, he, _, _, hl, hc⟩ := Unique.representation G k
  have hold : TwoBoundary.BinaryFrontend.value
      (TwoBoundary.BinaryFrontend.compile (Unique.build (ofGraph G k))) =
        Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
    rw [he, TwoBoundary.BinaryFrontend.compile_count]
    exact hc
  by_cases hn : n = 0
  · simpa only [compile, ofGraph, graph, IndependentDomination.ofGraph,
      IndependentDomination.order, hn, ↓reduceIte] using hold
  · have hn' : 1 ≤ n := by omega
    have hp : (TwoBoundary.BinaryFrontend.conditions (Unique.build (ofGraph G k))).isEmpty =
        false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have hz := List.isEmpty_iff_length_eq_zero.mp h
      have hlen := (layout (ofGraph G k)).2.2
      change _ = 3 * n at hlen
      omega
    have hnraw : IndependentDomination.order (graph (ofGraph G k)) ≠ 0 := hn
    rw [compile, ite_eq_right hnraw]
    change TwoBoundary.BinaryFrontend.value
      (.inr (oldDeclaration (ofGraph G k) + n, query (ofGraph G k) false,
        query (ofGraph G k) true)) = _
    simp only [TwoBoundary.BinaryFrontend.value]
    rw [query_count_eq G k hn' false, query_count_eq G k hn' true]
    simpa only [TwoBoundary.BinaryFrontend.compile, hp, Bool.false_eq_true, ↓reduceIte,
      TwoBoundary.BinaryFrontend.value, oldDeclaration] using hold

end Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers
