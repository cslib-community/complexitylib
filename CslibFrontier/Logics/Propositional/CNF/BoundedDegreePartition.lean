/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.PaddedCardinality
public import CslibFrontier.Logics.Propositional.CNF.DegreePartition

/-!
# Functional per-class bounds on labeled degree partitions

Reuse the complete no-test matrix semantics and add independently functional interval tests in
uniform class blocks. Forgetting every gate/threshold counts ordinary bounded labeled partitions
exactly once. Source: [ChenJiangZhu2027], Theorem 7.3 / Appendix C.2, PDF pp.25,32.
## Main results

* `model_iff`: the approved matrix constraints coupled to uniquely determined class tests.
* `count_eq_partitions`: an explicit forgetful bijection to ordinary bounded labeled families.

-/

public section

namespace Cslib.Logic.PL.DegreePartition.Bounded

open DegreeThreshold

/-- Original class bits, allocated functional gate slots, and target thresholds. -/
abbrev Vars (n q D : ℕ) := Fin q × DegreeThreshold.Vars n D (PaddedCardinality.capacity n)
/-- Insert the gate slots in each approved no-test class block. -/
@[expose] def embed {n q D : ℕ} (v : DegreePartition.Vars n q D) : Vars n q D :=
  (v.1, Sum.map (Fin.castAdd (PaddedCardinality.capacity n)) id v.2)
/-- The full selection/gate word of one class. -/
@[expose] def inputWire {n q D : ℕ} (i : Fin q) (j : Fin (n + PaddedCardinality.capacity n)) :
    Vars n q D := (i, Sum.inl j)
/-- Forget only gate slots, retaining all original class and threshold bits. -/
@[expose] def project {n q D : ℕ} (y : Vars n q D → Bool) : DegreePartition.Vars n q D → Bool :=
  y ∘ embed
/-- The full declared selection/gate word for one class. -/
@[expose] def classPrefix {n q D : ℕ} (y : Vars n q D → Bool) (i : Fin q) :
    Fin (n + PaddedCardinality.capacity n) → Bool := y ∘ inputWire i
/-- The actual no-test constraints and functional interval constraints share class selections. -/
@[expose] def side {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (F : Fin q → CNF (Fin (n + PaddedCardinality.capacity n))) : CNF (Vars n q D) :=
  (DegreePartition.side G q D hD M).relabel embed ++
    (List.finRange q).flatMap fun i => (F i).relabel (inputWire i)
/-- The qDv approved reverse predicates, with gate slots inserted. -/
@[expose] def conditions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q D : ℕ) : List (DNF (Vars n q D)) :=
  (DegreePartition.conditions G q D).map (CNF.relabel embed)
/-- Compute all padded gate traces and all original target thresholds from class membership. -/
@[expose] def extend {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (lo hi : Fin q → ℕ) (x : Fin q → Fin n → Bool) : Vars n q D → Bool :=
  fun p => Sum.elim (PaddedCardinality.values (lo p.1) (hi p.1) (x p.1))
    (fun t => decide (t.1.val + 1 ≤ count G (x p.1) t.2)) p.2

/-- Generated gate traces leave the old selection/threshold word unchanged. -/
theorem project_extend {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (lo hi : Fin q → ℕ) (x : Fin q → Fin n → Bool) :
    project (extend G D lo hi x) = DegreePartition.extend G D x := by
  funext v
  rcases v with ⟨i, v⟩
  cases v with
  | inl u => exact PaddedCardinality.values_input _ _ _ u
  | inr t => rfl

private theorem weight_card {n : ℕ} (x : Fin n → Bool) :
    Cslib.BitString.weight x = Nat.card {u | x u = true} := by
  rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
  rfl

/-- Pointwise functional size-test semantics, coupled to the approved no-test instance. -/
theorem model_iff {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (lo hi : Fin q → ℕ)
    (F : Fin q → CNF (Fin (n + PaddedCardinality.capacity n)))
    (hF : ∀ i, (F i).relabel Fin.val = PaddedCardinality.formula (n, lo i, hi i))
    (y : Vars n q D → Bool) :
    ((side G hD M F).eval y = true ∧ ∀ p ∈ conditions G q D, DNF.eval y p = true) ↔
      ((DegreePartition.side G q D hD M).eval (project y) = true ∧
        ∀ p ∈ DegreePartition.conditions G q D, DNF.eval (project y) p = true) ∧
      (∀ i, classPrefix y i = PaddedCardinality.values (lo i) (hi i)
        (DegreePartition.restrict (project y) i)) ∧
      SimpleGraph.InClassBounds lo hi
        (fun i => {u | DegreePartition.restrict (project y) i u = true}) := by
  have he (i : Fin q) : (F i).eval (classPrefix y i) =
      (PaddedCardinality.formula (n, lo i, hi i)).eval
        (Function.extend Fin.val (classPrefix y i) (fun _ => false)) := by
    rw [← hF i, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
  have hg (i : Fin q) : (F i).eval (classPrefix y i) = true ↔
      classPrefix y i = PaddedCardinality.values (lo i) (hi i)
        (DegreePartition.restrict (project y) i) ∧
      lo i ≤ Nat.card {u | DegreePartition.restrict (project y) i u = true} ∧
        Nat.card {u | DegreePartition.restrict (project y) i u = true} ≤ hi i := by
    rw [he]
    simpa only [weight_card] using PaddedCardinality.eval_iff (lo i) (hi i)
      (DegreePartition.restrict (project y) i) (classPrefix y i) (fun _ => rfl)
  simp only [side, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel,
    CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_const, conditions,
    List.forall_mem_map, DNF.eval_relabel]
  change ((_ ∧ ∀ i, (F i).eval (classPrefix y i) = true) ∧ _) ↔ _
  simp only [hg, forall_and, SimpleGraph.InClassBounds]
  tauto

open Classical in
/-- Each bounded labeled partition has exactly one full gate/threshold extension. -/
theorem count_eq_partitions {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (lo hi : Fin q → ℕ)
    (F : Fin q → CNF (Fin (n + PaddedCardinality.capacity n)))
    (hF : ∀ i, (F i).relabel Fin.val = PaddedCardinality.formula (n, lo i, hi i)) :
    Nat.card {y : Vars n q D → Bool // (side G hD M F).eval y = true ∧
      ∀ p ∈ conditions G q D, DNF.eval y p = true} =
      Nat.card {S : Fin q → Set (Fin n) // G.IsDegreePartition (fun i j => (M i j).counts) S ∧
        SimpleGraph.InClassBounds lo hi S} := by
  let f : {y : Vars n q D → Bool // (side G hD M F).eval y = true ∧
      ∀ p ∈ conditions G q D, DNF.eval y p = true} →
      {S : Fin q → Set (Fin n) // G.IsDegreePartition (fun i j => (M i j).counts) S ∧
        SimpleGraph.InClassBounds lo hi S} := fun y =>
    ⟨fun i => {u | DegreePartition.restrict (project y.val) i u = true},
      ((DegreePartition.model_iff G hD M _).mp
        ((model_iff G hD M lo hi F hF y.val).mp y.property).1).2,
      ((model_iff G hD M lo hi F hF y.val).mp y.property).2.2⟩
  apply Nat.card_congr
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    have hx := (model_iff G hD M lo hi F hF x.val).mp x.property
    have hy := (model_iff G hD M lo hi F hF y.val).mp y.property
    have hw : DegreePartition.restrict (project x.val) =
        DegreePartition.restrict (project y.val) := by
      funext i u
      exact Bool.eq_iff_iff.mpr (Set.ext_iff.mp (congrFun (congrArg Subtype.val he) i) u)
    apply Subtype.ext
    funext v
    rcases v with ⟨i, v⟩
    cases v with
    | inl u =>
      change classPrefix x.val i u = classPrefix y.val i u
      rw [hx.2.1 i, hy.2.1 i, hw]
    | inr t =>
      have hxt := ((DegreePartition.model_iff G hD M _).mp hx.1).1 i t.1 t.2
      have hyt := ((DegreePartition.model_iff G hD M _).mp hy.1).1 i t.1 t.2
      change project x.val (i, bit t.1 t.2) = project y.val (i, bit t.1 t.2)
      rw [hxt, hyt, hw]
  · rintro ⟨S, hm, hb⟩
    let words (i : Fin q) (u : Fin n) := decide (u ∈ S i)
    have hs : (fun i => {u | words i u = true}) = S := by funext i; ext u; simp [words]
    have hr : DegreePartition.restrict (project (extend G D lo hi words)) = words := by
      rw [project_extend]
      rfl
    refine ⟨⟨extend G D lo hi words, (model_iff G hD M lo hi F hF _).mpr ⟨?_, ?_, ?_⟩⟩, ?_⟩
    · apply (DegreePartition.model_iff G hD M _).mpr
      refine ⟨?_, ?_⟩
      · intro j t u
        change decide (t.val + 1 ≤ count G (words j) u) = _
        rw [hr]
      · simpa only [hr, hs] using hm
    · intro i
      change PaddedCardinality.values (lo i) (hi i) (words i) = _
      rw [hr]
    · simpa only [hr, hs] using hb
    · apply Subtype.ext
      simpa only [f, hr] using hs

/-- All actual gate clauses retain width three; thresholds retain their approved widths/count. -/
theorem widths {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (F : Fin q → CNF (Fin (n + PaddedCardinality.capacity n)))
    (hF : ∀ i, ∀ c ∈ F i, c.length ≤ 3) :
    (∀ c ∈ side G hD M F, c.length ≤ max q (max (D + 1) 3)) ∧
      (∀ p ∈ conditions G q D, ∀ t ∈ p, t.length ≤ D) ∧
      (conditions G q D).length = q * (D * n) := by
  obtain ⟨hb, hp, hl⟩ := DegreePartition.widths G hD M
  refine ⟨?_, ?_, by simpa only [conditions, List.length_map] using hl⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      simpa only [Clause.relabel, List.length_map] using hb t ht
    · obtain ⟨i, _, hmap⟩ := List.mem_flatMap.mp hc
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmap
      simp only [Clause.relabel, List.length_map]
      exact (hF i t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro p hmap t ht
    obtain ⟨localP, hlocalP, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨localT, hlocalT, rfl⟩ := List.mem_map.mp ht
    simpa only [Clause.relabel, List.length_map] using hp localP hlocalP localT hlocalT

end Cslib.Logic.PL.DegreePartition.Bounded
