/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.DegreeThreshold
public import CslibFrontier.Logics.Propositional.DNF.Relabel
import all CslibFrontier.Computability.PolyTime.CNF.DegreeThreshold

/-!
# General fixed-tail selected/unselected degree rules

State clauses apply arbitrary fixed finite/cofinite rules to the uniquely determined neighbor
thresholds. This is [ChenJiangZhu2027], Corollary 7.2 / Appendix C.2 (PDF pp.24–25,31–32).
-/

public section

namespace Cslib.Logic.PL.SigmaRho

open Turing.MultiTapeTM Cslib.Circuits.Boolean DegreeThreshold

/-- The bounded term recognizing a truncated count, including the entire tail at D. -/
@[expose] def finiteState {n D : ℕ} (hD : 1 ≤ D) (a : ℕ) (u : Fin n)
    (s : Fin (D + 1)) : Term (Vars n D a) :=
  if hs : s.val = 0 then [(bit ⟨0, by omega⟩ u, false)]
  else if he : s.val = D then [(bit ⟨D - 1, by omega⟩ u, true)]
  else [(bit ⟨s.val - 1, by omega⟩ u, true), (bit ⟨s.val, by omega⟩ u, false)]

/-- A correct threshold array recognizes exactly the actual truncated count state. -/
theorem state_eval {n D : ℕ} (hD : 1 ≤ D) (a : ℕ) (u : Fin n) (s : Fin (D + 1))
    (y : Vars n D a → Bool) (c : ℕ)
    (hy : ∀ j : Fin D, y (bit j u) = decide (j.val + 1 ≤ c)) :
    Term.eval y (finiteState hD a u s) = true ↔ min D c = s.val := by
  unfold finiteState
  split_ifs with hs he
  · simp [Term.eval, Literal.eval, hy]; omega
  · simp [Term.eval, Literal.eval, hy]; omega
  · simp [Term.eval, Literal.eval, hy]; omega

/-- All disallowed selected/unselected states at one original vertex. -/
@[expose] def finiteRuleAt {n D : ℕ} (hD : 1 ≤ D)
    (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ) (u : Fin n) : CNF (Vars n D a) :=
  (List.finRange (D + 1)).flatMap fun s =>
    (if σ s then [] else [Term.negate ((selection a u, true) :: finiteState hD a u s)]) ++
      (if ρ s then [] else [Term.negate ((selection a u, false) :: finiteState hD a u s)])
/-- Bounded state clauses on every original vertex. -/
@[expose] def finiteRules {n : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ) : CNF (Vars n D a) :=
  (List.finRange n).flatMap (finiteRuleAt hD σ ρ a)

/-- Ordinary selected-neighbor count agrees with the actual canonical neighbor-list traversal. -/
theorem count_eq_selectedDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (u : Fin n) :
    count G x u = G.selectedDegree {v | x v = true} u := by
  classical
  unfold count finiteNeighbors SimpleGraph.selectedDegree
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← List.toFinset_card_of_nodup
    (((List.nodup_finRange n).filter _).filter _)]
  congr 1
  ext v
  simp [and_comm]

private theorem forbidden_eval {V : Type*} (b : Bool) (t : Term V) (y : V → Bool) :
    CNF.eval y (if b then [] else [t.negate]) = true ↔ (Term.eval y t = true → b = true) := by
  cases b <;> simp [CNF.eval, Term.eval_negate]

/-- With functional thresholds, state clauses impose the actual selected/unselected rules. -/
theorem ruleAt_eval {n D : ℕ} (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D)
    (a : ℕ) (u : Fin n) (y : Vars n D a → Bool) (c : ℕ)
    (hy : ∀ j : Fin D, y (bit j u) = decide (j.val + 1 ≤ c)) :
    (finiteRuleAt hD σ ρ a u).eval y = true ↔
      (y (selection a u) = true → σ.accepts c = true) ∧
        (y (selection a u) = false → ρ.accepts c = true) := by
  have hr : (finiteRuleAt hD σ ρ a u).eval y = true ↔ ∀ s : Fin (D + 1),
      CNF.eval y (if σ s then [] else
        [Term.negate ((selection a u, true) :: finiteState hD a u s)]) = true ∧
      CNF.eval y (if ρ s then [] else
        [Term.negate ((selection a u, false) :: finiteState hD a u s)]) = true := by
    simp only [finiteRuleAt, CNF.eval_eq_true_iff, List.forall_mem_flatMap,
      List.mem_finRange, forall_const, List.forall_mem_append]
  rw [hr]
  simp only [forbidden_eval, Term.eval_cons, Bool.and_eq_true, Literal.eval_eq_true_iff,
    state_eval hD a u _ y c hy]
  let s : Fin (D + 1) := ⟨min D c, by have := Nat.min_le_left D c; omega⟩
  constructor
  · intro h
    exact ⟨fun hx => (h s).1 ⟨hx, rfl⟩, fun hx => (h s).2 ⟨hx, rfl⟩⟩
  · rintro ⟨hs, hr⟩ t
    constructor
    · rintro ⟨hx, he⟩
      have ht : t = s := Fin.ext he.symm
      rw [ht]
      exact hs hx
    · rintro ⟨hx, he⟩
      have ht : t = s := Fin.ext he.symm
      rw [ht]
      exact hr hx

/-- Derived thresholds make the rule formula match conventional sigma-rho sets. -/
theorem rules_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ)
    (y : Vars n D a → Bool)
    (hy : ∀ (j : Fin D) (u : Fin n), y (bit j u) =
      decide (j.val + 1 ≤ count G (fun v => y (selection a v)) u)) :
    (finiteRules (n := n) D hD σ ρ a).eval y = true ↔
      G.IsSigmaRhoSet σ.counts ρ.counts {u | y (selection a u) = true} := by
  have hr : (finiteRules (n := n) D hD σ ρ a).eval y = true ↔
      ∀ u : Fin n, (finiteRuleAt hD σ ρ a u).eval y = true := by
    simp only [finiteRules, CNF.eval_eq_true_iff, List.forall_mem_flatMap,
      List.mem_finRange, forall_const]
  rw [hr]
  simp only [ruleAt_eval hD σ ρ a _ y _ (fun j => hy j _), count_eq_selectedDegree,
    SimpleGraph.IsSigmaRhoSet, SimpleGraph.DegreeRule.counts, Set.mem_ofPred_eq]
  apply forall_congr'
  intro u
  cases y (selection a u) <;> simp


/-- Canonical threshold extension of any original selection/gate prefix. -/
@[expose] def extend {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D a : ℕ)
    (x : Fin (n + a) → Bool) : Vars n D a → Bool :=
  Sum.elim x (fun p => decide (p.1.val + 1 ≤ count G (fun u => x (Fin.castAdd a u)) p.2))
/-- The original side formula and all threshold/state clauses share one declared word. -/
@[expose] def finiteBase {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ)
    (F : CNF (Fin (n + a))) : CNF (Vars n D a) :=
  F.relabel Sum.inl ++ finiteForward G D a ++ finiteRules D hD σ ρ a

/-- Whole-formula pointwise semantics retain the original prefix and derive every threshold. -/
theorem model_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ)
    (F : CNF (Fin (n + a))) (y : Vars n D a → Bool) :
    ((finiteBase G D hD σ ρ a F).eval y = true ∧
      ∀ p ∈ finiteReverse G D a, DNF.eval y p = true) ↔
    F.eval (y ∘ Sum.inl) = true ∧
      (∀ (j : Fin D) (u : Fin n), y (bit j u) =
        decide (j.val + 1 ≤ count G (fun v => y (selection a v)) u)) ∧
      G.IsSigmaRhoSet σ.counts ρ.counts {u | y (selection a u) = true} := by
  simp only [finiteBase, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel]
  constructor
  · rintro ⟨⟨⟨hF, hf⟩, hr⟩, hp⟩
    have hy := (functional G D a y).mp ⟨hf, hp⟩
    exact ⟨hF, hy, (rules_eval G D hD σ ρ a y hy).mp hr⟩
  · rintro ⟨hF, hy, hs⟩
    obtain ⟨hf, hp⟩ := (functional G D a y).mpr hy
    exact ⟨⟨⟨hF, hf⟩, (rules_eval G D hD σ ρ a y hy).mpr hs⟩, hp⟩

open Classical in
/-- Forgetting the uniquely derived threshold array preserves original-prefix counts, even with
an arbitrary independent gate formula on that prefix. -/
theorem count_extensions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ)
    (F : CNF (Fin (n + a))) :
    Nat.card {y : Vars n D a → Bool // (finiteBase G D hD σ ρ a F).eval y = true ∧
      ∀ p ∈ finiteReverse G D a, DNF.eval y p = true} =
      Nat.card {x : Fin (n + a) → Bool // F.eval x = true ∧
        G.IsSigmaRhoSet σ.counts ρ.counts {u | x (Fin.castAdd a u) = true}} := by
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨y.val ∘ Sum.inl, ((model_iff G D hD σ ρ a F y.val).mp y.property).1,
        ((model_iff G D hD σ ρ a F y.val).mp y.property).2.2⟩
      invFun := fun x => ⟨extend G D a x.val,
        (model_iff G D hD σ ρ a F _).mpr ⟨x.property.1, fun _ _ => rfl, x.property.2⟩⟩
      left_inv := fun y => by
        apply Subtype.ext
        funext v
        cases v with
        | inl i => rfl
        | inr p =>
          exact (((model_iff G D hD σ ρ a F y.val).mp y.property).2.1 p.1 p.2).symm
      right_inv := fun _ => rfl }

open Classical in
/-- Coordinate erasure to the finite declared wire set preserves the actual joint model count. -/
theorem count_relabel {n D a : ℕ} (B : CNF (Vars n D a)) (P : List (DNF (Vars n D a))) :
    Nat.card {y : Fin ((n + a) + D * n) → Bool //
      (B.relabel (wireEquiv n D a)).eval y = true ∧
        ∀ p ∈ P.map (CNF.relabel (wireEquiv n D a)), DNF.eval y p = true} =
      Nat.card {y : Vars n D a → Bool // B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} := by
  let e : (Fin ((n + a) + D * n) → Bool) ≃ (Vars n D a → Bool) :=
    Equiv.arrowCongr (wireEquiv n D a).symm (Equiv.refl Bool)
  apply Nat.card_congr
  exact e.subtypeEquiv fun _ => by
    simp only [CNF.eval_relabel, List.forall_mem_map, DNF.eval_relabel]
    rfl


/-- Raw bounded state term, with the last state representing all counts at least D. -/
@[expose] def state (D : ℕ) (x : Core) (s u : ℕ) : Term ℕ :=
  if s = 0 then [(DegreeThreshold.threshold x 0 u, false)]
  else if s = D then [(DegreeThreshold.threshold x (D - 1) u, true)]
  else [(DegreeThreshold.threshold x (s - 1) u, true), (DegreeThreshold.threshold x s u, false)]
/-- Actual fixed-rule forbidden-state clauses on original selection and threshold wires. -/
@[expose] def rules (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) (x : Core) : CNF ℕ :=
  (List.range (IndependentDomination.order (graph x))).flatMap fun u =>
    (List.range (D + 1)).flatMap fun s =>
      (if (List.ofFn σ).getD s false then [] else [Term.negate ((u, true) :: state D x s u)]) ++
      (if (List.ofFn ρ).getD s false then [] else [Term.negate ((u, false) :: state D x s u)])

private abbrev encClause := encList (encPair encNat encBool)

private theorem state_polytime (D s : ℕ) : ComputableInPolyTime
    (fun p : Core × ℕ => state D p.1 s p.2) encRow encClause := by
  have h0 := index_polytime 0
  have hD := index_polytime (D - 1)
  have hs := index_polytime (s - 1)
  have ht := index_polytime s
  unfold state
  split_ifs <;> unfold encClause <;> fun_prop

private theorem negate_polytime : ComputableInPolyTime (Term.negate : Term ℕ → Clause ℕ)
    encClause encClause := by
  unfold Term.negate encClause
  fun_prop

/-- Fixed rule tables have charged graph traversal and binary state-clause writing. -/
@[fun_prop] theorem rules_polytime (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) :
    ComputableInPolyTime (rules D σ ρ) encCore VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encCore encUnary := by
    unfold graph encCore IndependentDomination.order IndependentDomination.encInput; fun_prop
  unfold rules
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.flatMapConst
  intro s _
  have ht := state_polytime D s
  have hu : ComputableInPolyTime (fun p : Core × ℕ => p.2) encRow encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
  have hterm (b : Bool) : ComputableInPolyTime
      (fun p : Core × ℕ => (p.2, b) :: state D p.1 s p.2) encRow encClause := by
    unfold encClause at *; fun_prop
  have hneg (b : Bool) := negate_polytime.comp (hterm b)
  have hbody (b : Bool) : ComputableInPolyTime
      (fun p : Core × ℕ => [Term.negate ((p.2, b) :: state D p.1 s p.2)])
      encRow VCOne.encSignedCNF := by
    unfold VCOne.encSignedCNF encClause at *; fun_prop
  exact ComputableInPolyTime.listAppend'
    ((show ComputableInPolyTime (fun _ : Core × ℕ => (List.ofFn σ).getD s false)
      encRow encBool from .const _).ite' (.const []) (hbody true))
    ((show ComputableInPolyTime (fun _ : Core × ℕ => (List.ofFn ρ).getD s false)
      encRow encBool from .const _).ite' (.const []) (hbody false))

/-- Canonical finite state recognition erases to the actual bounded state term. -/
theorem state_ofGraph {n D : ℕ} (hD : 1 ≤ D) (a : ℕ) (u : Fin n) (s : Fin (D + 1))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    state D (IndependentDomination.ofGraph G, n + a) s.val u.val =
      Clause.relabel (fun v => (wireEquiv n D a v).val) (finiteState hD a u s) := by
  unfold state finiteState
  split_ifs <;> rfl

/-- The actual compiled fixed rule tables preserve the finite source state formula. -/
theorem rules_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ) :
    rules D σ ρ (IndependentDomination.ofGraph G, n + a) =
      (finiteRules D hD σ ρ a).relabel (fun v => (wireEquiv n D a v).val) := by
  simp only [rules, finiteRules, graph, IndependentDomination.order,
    IndependentDomination.ofGraph, ← List.map_coe_finRange_eq_range, List.flatMap_map,
    CNF.relabel, List.map_flatMap]
  congr 1
  funext u
  simp only [finiteRuleAt, List.map_flatMap]
  congr 1
  funext s
  have h (b : Bool) : Clause.relabel (fun v => (wireEquiv n D a v).val)
      (Term.negate ((selection a u, b) :: finiteState hD a u s)) =
        Term.negate ((u.val, b) ::
          state D (IndependentDomination.ofGraph G, n + a) s.val u.val) := by
    rw [Term.negate_relabel]
    apply congrArg Term.negate
    change (u.val, b) :: Clause.relabel (fun v => (wireEquiv n D a v).val)
      (finiteState hD a u s) = _
    rw [← state_ofGraph hD a u s G]
  have hσ := List.getD_ofFn σ s false
  have hρ := List.getD_ofFn ρ s false
  rw [hσ, hρ]
  cases hs : σ s <;> cases hr : ρ s <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.map_append,
      List.map_nil, List.map_singleton, h] <;> rfl

/-- State terms have at most two literals, so all selected/unselected guards have width three. -/
theorem rule_widths {n D : ℕ} (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ) :
    ∀ c ∈ finiteRules (n := n) D hD σ ρ a, c.length ≤ 3 := by
  intro c hc
  simp only [finiteRules, finiteRuleAt, List.mem_flatMap, List.mem_finRange, true_and] at hc
  obtain ⟨u, s, hc⟩ := hc
  have hs : (finiteState hD a u s).length ≤ 2 := by
    unfold finiteState
    split_ifs <;> simp
  rcases List.mem_append.mp hc with hc | hc <;> split_ifs at hc <;>
    simp_all only [List.not_mem_nil, List.mem_singleton, Term.negate, List.length_map,
      List.length_cons] <;> omega

/-- Two forbidden-state clauses per fixed state and original vertex suffice for arbitrary rules. -/
theorem rule_volume (n D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (a : ℕ) :
    (finiteRules (n := n) D hD σ ρ a).length ≤ 2 * (D + 1) * n := by
  have hu (u : Fin n) : (finiteRuleAt hD σ ρ a u).length ≤ 2 * (D + 1) := by
    simp only [finiteRuleAt, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn,
      Function.comp_def]
    calc
      _ ≤ ∑ _s : Fin (D + 1), 2 := by
        apply Finset.sum_le_sum
        intro s _
        cases σ s <;> cases ρ s <;> simp
      _ = _ := by simp; omega
  simp only [finiteRules, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  calc
    _ ≤ ∑ _u : Fin n, 2 * (D + 1) := Finset.sum_le_sum fun u _ => hu u
    _ = _ := by simp; ring

end Cslib.Logic.PL.SigmaRho
