/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.TwoBoundaryFrontend
import all CslibFrontier.Logics.Propositional.CNF.ExactOnePathPlan
public import CslibFrontier.Computability.PolyTime.CNF.WeightedPlan
import all CslibFrontier.Computability.PolyTime.CNF.WeightedPlan

/-!
# Original-count correctness and exact budgets of the generic DNF writer

This is the actual encoded constructor of [ChenJiangZhu2027], Theorem 1.1, PDF pp. 4–5.
The theorem allows arbitrary overlap, terms, conditions and unused declared bits. Unlike the
separate table theorem, it imposes no VC-dimension promise and never expands a relation table.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary.BinaryFrontend

open WeightedRow

/-- Explicit finite formulas with only their bounded original variable labels erased. -/
@[expose] def ofFinite {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n))) : Input :=
  (n, B.relabel Fin.val, P.map (CNF.relabel Fin.val))

/-- All actually emitted ordinary queries, retaining their declared variable counts. -/
@[expose] def queries : Output → List (ℕ × CNF ℕ)
  | .inl q => [q]
  | .inr (N, qf, qt) => [(N, qf), (N, qt)]

/-- Exact ordinary declared model counts and, in the nonempty case, their subtraction. -/
@[expose] noncomputable def value : Output → ℕ
  | .inl (N, q) => BinaryPlan.queryCount N q
  | .inr (N, qf, qt) => BinaryPlan.queryCount N qf - BinaryPlan.queryCount N qt

/-- The executable binary lists are exactly the ordinary reviewed path queries. -/
theorem query_relabel {n h : ℕ} (B : CNF (Fin n))
    (P : Fin (h + 1) → DNF (Fin n)) (β : Bool) :
    query (ofFinite B (List.ofFn P)) β =
      (TwoBoundary.query B h P β).relabel (BinaryQuery.flattenVar (n := n)) := by
  have he (j : Fin (h + 1)) :
      ((List.ofFn P).map (CNF.relabel Fin.val)).getD j.val [] =
        CNF.relabel Fin.val (P j) := by
    rw [List.map_ofFn]
    exact List.getD_ofFn _ j []
  simp only [query, ofFinite, side, declared, conditions, List.length_map,
    List.length_ofFn, Nat.add_sub_cancel]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, he, CNF.relabel]
  simp only [TwoBoundary.query, CNF.relabel, List.map_append, List.map_flatMap,
    List.map_map, Function.comp_def]
  congr 1
  · congr 1
    funext c
    simp only [Clause.relabel, List.map_map, Function.comp_def]
    rfl
  · congr 1
    funext j
    congr 1
    funext t
    exact BinaryQuery.termClauses_eq β j t

/-- Exact original declared-assignment count of the actual one/two-query dispatcher.
Empty/contradictory terms and arbitrary overlaps require no additional promise. -/
theorem compile_count {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n))) :
    value (compile (ofFinite B P)) =
      Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true} := by
  classical
  by_cases hp : P = []
  · subst P
    simp only [compile, conditions, ofFinite, List.map_nil, List.isEmpty_nil,
      ↓reduceIte, declared, side, value]
    rw [ExactOne.BinaryPlan.queryCount_fin]
    unfold ExactOne.declaredCount
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight fun _ => by simp
  have hl : 0 < P.length := List.length_pos_iff.mpr hp
  let h := P.length - 1
  have hh : h + 1 = P.length := by dsimp only [h]; omega
  let F : Fin (h + 1) → DNF (Fin n) := fun j => P.get (Fin.cast hh j)
  have hF : List.ofFn F = P := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; exact hh
    · intro i hi hj
      simp only [F, List.getElem_ofFn, List.get_eq_getElem]
      rfl
  have hn : (List.ofFn F).isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hz := congrArg List.length (List.isEmpty_iff.mp he)
    simp only [List.length_ofFn, List.length_nil] at hz
    omega
  have hN : n + (h + 1) - 1 = n + h := by omega
  rw [← hF]
  simp only [compile, conditions, ofFinite, List.isEmpty_map, hn, Bool.false_eq_true,
    ↓reduceIte, declared, List.length_map, List.length_ofFn,
    hN, value]
  change BinaryPlan.queryCount (n + h) (query (ofFinite B (List.ofFn F)) false) -
    BinaryPlan.queryCount (n + h) (query (ofFinite B (List.ofFn F)) true) = _
  rw [query_relabel, query_relabel, BinaryPlan.queryCount_relabel,
    BinaryPlan.queryCount_relabel, ← TwoBoundary.counting_identity]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]

/-- Exactly one query for no conditions and two queries otherwise. -/
theorem compile_query_count (x : Input) :
    (queries (compile x)).length = if (conditions x).isEmpty then 1 else 2 := by
  unfold compile
  split_ifs <;> rfl

/-- Exact source declaration, clause, width and literal-index budgets for every emitted query. -/
theorem compile_budget {n b d : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (hb : ∀ c ∈ B, c.length ≤ b) (hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d)
    (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ queries (compile (ofFinite B P))) :
    N = (if P.isEmpty then n else n + P.length - 1) ∧
      q.length ≤ B.length + 2 * (P.map List.length).sum ∧
      ∀ c ∈ q, c.length ≤ max b (d + 2) ∧ ∀ l ∈ c, l.1 < N := by
  classical
  by_cases he : P = []
  · subst P
    simp only [compile, conditions, ofFinite, List.map_nil, List.isEmpty_nil,
      ↓reduceIte, declared, side, queries, List.mem_singleton, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    refine ⟨rfl, ?_, ?_⟩
    · simp [CNF.relabel]
    · intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      refine ⟨by simpa only [Clause.relabel, List.length_map] using
        (hb a ha).trans (le_max_left _ _), ?_⟩
      intro l hl
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
      exact a.1.isLt
  have hl : 0 < P.length := List.length_pos_iff.mpr he
  let h := P.length - 1
  have hh : h + 1 = P.length := by dsimp only [h]; omega
  let F : Fin (h + 1) → DNF (Fin n) := fun j => P.get (Fin.cast hh j)
  have hF : List.ofFn F = P := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; exact hh
    · intro i hi hj
      simp only [F, List.getElem_ofFn, List.get_eq_getElem]
      rfl
  have hn : (List.ofFn F).isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hz := congrArg List.length (List.isEmpty_iff.mp he)
    simp only [List.length_ofFn, List.length_nil] at hz
    omega
  have hN : n + (h + 1) - 1 = n + h := by omega
  rw [← hF] at hq ⊢
  simp only [compile, conditions, ofFinite, List.isEmpty_map, hn, Bool.false_eq_true,
    ↓reduceIte, declared, List.length_map, List.length_ofFn,
    hN, queries, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hq
  have hbudget (β : Bool) :
      (query (ofFinite B (List.ofFn F)) β).length ≤
        B.length + 2 * ((List.ofFn F).map List.length).sum ∧
      ∀ c ∈ query (ofFinite B (List.ofFn F)) β,
        c.length ≤ max b (d + 2) ∧ ∀ l ∈ c, l.1 < n + h := by
    rw [query_relabel]
    refine ⟨?_, ?_⟩
    · simp only [CNF.relabel, List.length_map, List.map_ofFn, List.sum_ofFn]
      exact TwoBoundary.query_length B F β
    · intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      refine ⟨?_, ?_⟩
      · simpa only [Clause.relabel, List.length_map] using TwoBoundary.query_width B F b d hb
          (fun j t ht => hp (F j) (by rw [← hF]; exact List.mem_ofFn.mpr ⟨j, rfl⟩) t ht) β a ha
      · intro l hl
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
        exact BinaryQuery.flattenVar_lt a.1
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals refine ⟨by simp, ?_⟩
  · exact hbudget false
  · exact hbudget true

end Cslib.Logic.PL.TwoBoundary.BinaryFrontend
