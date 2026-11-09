/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.SimpleGraph.DegreePartition
public import Complexity.Computability.PolyTime.CNF.SigmaRho
public import Complexity.Logics.Propositional.CNF.ExactlyOneRelabel
import all Complexity.Computability.PolyTime.CNF.SigmaRho

/-!
# Functional labeled degree-matrix partition construction

Actual one-hot clauses share original class selections with one threshold vector per target class.
No edge/subset certificate is introduced. Source: [ChenJiangZhu2027], Theorem 7.3 / Appendix C.2,
PDF pp.25,32. The no-size-test construction is separated from class-size gate frontends.
-/

public section

namespace Cslib.Logic.PL.DegreePartition

open DegreeThreshold

/-- One block of original selections and actual thresholds for each labeled class. -/
abbrev Vars (n q D : ℕ) := Fin q × DegreeThreshold.Vars n D 0
/-- The original class-membership bit. -/
@[expose] def selection {n q D : ℕ} (i : Fin q) (u : Fin n) : Vars n q D :=
  (i, DegreeThreshold.selection 0 u)
/-- Actual per-vertex one-hot clauses; repeated ordered exclusions only repeat constraints. -/
@[expose] def oneHot (n q D : ℕ) : CNF (Vars n q D) :=
  (List.finRange n).flatMap fun u => CNF.exactlyOne ((List.finRange q).map fun i => selection i u)
/-- A source-class implication tests the target class's actual truncated degree state. -/
@[expose] def ruleAt {n q D : ℕ} (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (i j : Fin q) (u : Fin n) : CNF (Vars n q D) :=
  (List.finRange (D + 1)).flatMap fun s =>
    if M i j s then [] else
      [Term.negate ((selection i u, true) ::
        Clause.relabel (Prod.mk j) (SigmaRho.finiteState hD 0 u s))]
/-- All matrix entries are imposed, without identifying or permuting their labels. -/
@[expose] def rules (n q D : ℕ) (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) : CNF (Vars n q D) :=
  (List.finRange q).flatMap fun i => (List.finRange q).flatMap fun j =>
    (List.finRange n).flatMap (ruleAt hD M i j)
/-- Full bounded side formula, sharing class bits across all target-neighbor tests. -/
@[expose] def side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q D : ℕ) (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) : CNF (Vars n q D) :=
  oneHot n q D ++ ((List.finRange q).flatMap fun j =>
    (finiteForward G D 0).relabel (Prod.mk j)) ++ rules n q D hD M
/-- Exactly qDv reverse predicates; each class has its own functional threshold block. -/
@[expose] def conditions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q D : ℕ) : List (DNF (Vars n q D)) :=
  (List.finRange q).flatMap fun j => (finiteReverse G D 0).map (CNF.relabel (Prod.mk j))
/-- Original membership words, forgetting all thresholds. -/
@[expose] def restrict {n q D : ℕ} (y : Vars n q D → Bool) (i : Fin q) (u : Fin n) : Bool :=
  y (selection i u)
/-- Unique threshold extension, computed separately from each target class's original word. -/
@[expose] def extend {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (x : Fin q → Fin n → Bool) : Vars n q D → Bool :=
  fun p => SigmaRho.extend G D 0 (x p.1) p.2

/-- The one-hot writer is precisely a labeled, possibly empty partition of original vertices. -/
theorem oneHot_eval {n q D : ℕ} (y : Vars n q D → Bool) :
    (oneHot n q D).eval y = true ↔ ∀ u, ∃! i, restrict y i u = true := by
  simp only [oneHot, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_const]
  apply forall_congr'
  intro u
  rw [CNF.eval_exactlyOne]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨⟨i, hi⟩, hu⟩
    exact ⟨i, hi, fun j hj => Prod.mk.inj (hu j i hj hi) |>.1⟩
  · rintro ⟨i, hi, hu⟩
    exact ⟨⟨i, hi⟩, fun j k hj hk => congrArg (fun i => selection i u)
      ((hu j hj).trans (hu k hk).symm)⟩

/-- Each forbidden state is equivalent to the ordinary source-class/target-count implication. -/
theorem ruleAt_eval {n q D : ℕ} (hD : 1 ≤ D)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (i j : Fin q) (u : Fin n)
    (y : Vars n q D → Bool) (c : ℕ)
    (hy : ∀ t : Fin D, y (j, bit t u) = decide (t.val + 1 ≤ c)) :
    (ruleAt hD M i j u).eval y = true ↔
      (restrict y i u = true → (M i j).accepts c = true) := by
  have ht (s : Fin (D + 1)) : Term.eval y
      (Clause.relabel (Prod.mk j) (SigmaRho.finiteState hD 0 u s)) = true ↔ min D c = s.val := by
    have he : Term.eval y
        (Clause.relabel (Prod.mk j) (SigmaRho.finiteState hD 0 u s)) =
          Term.eval (fun v => y (j, v)) (SigmaRho.finiteState hD 0 u s) := by
      simp only [Term.eval, Clause.relabel, List.all_map]
      rfl
    rw [he]
    exact SigmaRho.state_eval hD 0 u s (fun v => y (j, v)) c hy
  simp only [ruleAt, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_const,
    SigmaRho.forbidden_eval, Term.eval_cons, Bool.and_eq_true, Literal.eval_eq_true_iff, ht]
  let s : Fin (D + 1) := ⟨min D c, by have := Nat.min_le_left D c; omega⟩
  constructor
  · intro h hx
    exact h s ⟨hx, rfl⟩
  · intro h t ⟨hx, he⟩
    have hh : t = s := Fin.ext he.symm
    subst t
    exact h hx

/-- Exact pointwise semantics: all target thresholds are derived, not supplied as a promise. -/
theorem model_iff {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (y : Vars n q D → Bool) :
    ((side G q D hD M).eval y = true ∧ ∀ p ∈ conditions G q D, DNF.eval y p = true) ↔
      (∀ (j : Fin q) (t : Fin D) (u : Fin n), y (j, bit t u) =
        decide (t.val + 1 ≤ count G (restrict y j) u)) ∧
      G.IsDegreePartition (fun i j => (M i j).counts) (fun i => {u | restrict y i u = true}) := by
  have hf : CNF.eval y ((List.finRange q).flatMap fun j =>
      (finiteForward G D 0).relabel (Prod.mk j)) = true ↔
      ∀ j : Fin q, (finiteForward G D 0).eval (fun v => y (j, v)) = true := by
    simp only [CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_const, CNF.eval_relabel]
    rfl
  have hp : (∀ p ∈ conditions G q D, DNF.eval y p = true) ↔
      ∀ j : Fin q, ∀ p ∈ finiteReverse G D 0, DNF.eval (fun v => y (j, v)) p = true := by
    simp only [conditions, List.forall_mem_flatMap, List.mem_finRange, forall_const,
      List.forall_mem_map, DNF.eval_relabel]
    rfl
  have hr (hy : ∀ (j : Fin q) (t : Fin D) (u : Fin n), y (j, bit t u) =
      decide (t.val + 1 ≤ count G (restrict y j) u)) :
      (rules n q D hD M).eval y = true ↔
        ∀ i j u, restrict y i u = true →
          G.selectedDegree {v | restrict y j v = true} u ∈ (M i j).counts := by
    simp only [rules, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_const]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro j
    apply forall_congr'
    intro u
    rw [ruleAt_eval hD M i j u y _ (fun t => hy j t u)]
    simp only [SigmaRho.count_eq_selectedDegree, SimpleGraph.DegreeRule.counts,
      Set.mem_ofPred_eq]
  simp only [side, CNF.eval_append, Bool.and_eq_true, hf, hp, oneHot_eval,
    SimpleGraph.IsDegreePartition, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨ho, hforward⟩, hmatrix⟩, hreverse⟩
    have hy j := (functional G D 0 (fun v => y (j, v))).mp ⟨hforward j, hreverse j⟩
    exact ⟨hy, ho, (hr hy).mp hmatrix⟩
  · rintro ⟨hy, ho, hm⟩
    have hlocal j := (functional G D 0 (fun v => y (j, v))).mpr (hy j)
    exact ⟨⟨⟨ho, fun j => (hlocal j).1⟩, (hr hy).mpr hm⟩, fun j => (hlocal j).2⟩

open Classical in
/-- Forgetting thresholds is a bijection, so labeled partitions have no annotation multiplicity. -/
theorem count_eq_partitions {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    Nat.card {y : Vars n q D → Bool // (side G q D hD M).eval y = true ∧
      ∀ p ∈ conditions G q D, DNF.eval y p = true} =
      Nat.card {S : Fin q → Set (Fin n) // G.IsDegreePartition (fun i j => (M i j).counts) S} := by
  let f : {y : Vars n q D → Bool // (side G q D hD M).eval y = true ∧
      ∀ p ∈ conditions G q D, DNF.eval y p = true} →
      {S : Fin q → Set (Fin n) // G.IsDegreePartition (fun i j => (M i j).counts) S} :=
    fun y => ⟨fun i => {u | restrict y.val i u = true}, ((model_iff G hD M y.val).mp y.property).2⟩
  apply Nat.card_congr
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    have hwords : restrict x.val = restrict y.val := by
      funext i u
      have hh := Set.ext_iff.mp (congrFun (congrArg Subtype.val he) i) u
      change (restrict x.val i u = true) ↔ (restrict y.val i u = true) at hh
      exact Bool.eq_iff_iff.mpr hh
    apply Subtype.ext
    funext v
    rcases v with ⟨j, v⟩
    cases v with
    | inl u => exact congrFun (congrFun hwords j) u
    | inr p =>
      change x.val (j, bit p.1 p.2) = y.val (j, bit p.1 p.2)
      rw [((model_iff G hD M x.val).mp x.property).1,
        ((model_iff G hD M y.val).mp y.property).1, hwords]
  · rintro ⟨S, hs⟩
    let words (i : Fin q) (u : Fin n) := decide (u ∈ S i)
    have he : (fun i => {u | words i u = true}) = S := by funext i; ext u; simp [words]
    have hx' : restrict (extend G D words) = words := rfl
    refine ⟨⟨extend G D words, (model_iff G hD M _).mpr ⟨?_, ?_⟩⟩, ?_⟩
    · intro j t u
      change decide (t.val + 1 ≤ count G (words j) u) = _
      rw [hx']
    · simpa only [hx', he] using hs
    · apply Subtype.ext
      exact he

/-- Actual side/term widths and exact reverse-predicate count of the class-matrix construction. -/
theorem widths {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    (∀ c ∈ side G q D hD M, c.length ≤ max q (max (D + 1) 3)) ∧
      (∀ p ∈ conditions G q D, ∀ t ∈ p, t.length ≤ D) ∧
      (conditions G q D).length = q * (D * n) := by
  obtain ⟨hf, hp, hl⟩ := DegreeThreshold.widths G D 0 hD
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨u, _, hc⟩ := List.mem_flatMap.mp hc
        have hw := CNF.width_exactlyOne _ c hc
        simp only [List.length_map, List.length_finRange] at hw
        omega
      · obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
        simpa only [Clause.relabel, List.length_map] using
          (hf t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
    · simp only [rules, List.mem_flatMap] at hc
      obtain ⟨i, _, j, _, u, _, hc⟩ := hc
      simp only [ruleAt, List.mem_flatMap] at hc
      obtain ⟨st, _, hc⟩ := hc
      split_ifs at hc
      · simp at hc
      · have he := List.mem_singleton.mp hc
        subst c
        have hs : (SigmaRho.finiteState hD 0 u st).length ≤ 2 := by
          unfold SigmaRho.finiteState
          split_ifs <;> simp
        simp only [Term.negate, List.length_map, List.length_cons, Clause.relabel]
        omega
  · intro p hcondition t hterm
    obtain ⟨j, _, hmap⟩ := List.mem_flatMap.mp hcondition
    obtain ⟨localP, hlocalP, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨localT, hlocalT, rfl⟩ := List.mem_map.mp hterm
    simpa only [Clause.relabel, List.length_map] using hp localP hlocalP localT hlocalT
  · simp [conditions, List.length_flatMap, List.finRange, List.sum_ofFn, hl]

end Cslib.Logic.PL.DegreePartition
