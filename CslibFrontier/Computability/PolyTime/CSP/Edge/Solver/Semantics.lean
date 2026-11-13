/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Solver.Optimize
public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Guard
import Mathlib.Data.List.GetD

/-!
# Guarded explicit-table optimization and satisfiability

Initial local labels are actual first stored rows. The full model guard rejects empty or
malformed relations and repeated scope variables. Optimization uses the complete original
contraction/lifting mathematics. Its finite output is in the existing occurrence-list order.

The functions in this module specify the executable result; native multitape polynomial-time
realization additionally requires finite implementations and encoded storage bounds.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver

open Cslib.Logic.PL Cslib.Logic.PL.CSP

/-- One actual first stored row per original constraint. A missing row defaults to `[]`;
the full model guard rejects it, including a false nullary relation. -/
@[expose] def initialRows (F : CSP Table ℕ) : List (List Bool) :=
  F.map fun c => c.rel.rows.headD []

/-- The initial positional labeling, with no global assignment search. -/
@[expose] def initial (F : CSP Table ℕ) : OccurrenceLabeling F Bool :=
  Blossom.labels F (initialRows F)

/-- Every initial stored row is accepted and has exactly its actual scope width. -/
theorem initialRows_spec (F : CSP Table ℕ) (h : checkModel F = true) (i : Fin F.length) :
    F[i.val].rel.sem ((initialRows F).getD i.val []) = true ∧
      ((initialRows F).getD i.val []).length = F[i.val].scope.length := by
  have hc : F.all checkConstraint = true := by
    have hh : checkEdge F = true ∧ F.all checkConstraint = true := by
      simpa only [checkModel, Bool.and_eq_true] using h
    exact hh.2
  have hrow (i : Fin F.length) :
      F[i.val].rel.sem ((initialRows F).getD i.val []) = true ∧
      ((initialRows F).getD i.val []).length = F[i.val].scope.length := by
    have hi := List.all_eq_true.mp hc _ (List.getElem_mem i.isLt)
    simp only [checkConstraint, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hi
    have hw := hi.1.1.1
    have ha := hi.1.1.2
    have hn := hi.1.2
    have hm : F[i.val].rel.rows.headD [] ∈ F[i.val].rel.rows := by
      cases he : F[i.val].rel.rows with
      | nil => exact (hn he).elim
      | cons r rs => simp
    have he : (initialRows F).getD i.val [] = F[i.val].rel.rows.headD [] := by
      simp [initialRows, i.isLt]
    rw [he]
    exact ⟨Table.sem_eq_true.mpr ⟨hw, hm⟩,
      (Table.wellFormed_eq_true.mp hw _ hm).trans ha⟩
  exact hrow i

/-- Choosing one actual first stored row per constraint gives valid occurrence labels,
including true nullaries and repeated stored rows. -/
theorem initial_valid (F : CSP Table ℕ) (h : checkModel F = true) :
    ValidLabeling Table.sem (initial F) :=
  Blossom.valid_labels F (initialRows F)
    (fun i => (initialRows_spec F h i).2) (fun i => (initialRows_spec F h i).1)

/-- Guarded minimum-defect finite occurrence buffer. `none` means an input outside the model,
not an unsatisfiable valid model. -/
@[expose] def optimize (F : CSP Table ℕ) : Option (List Bool) :=
  if checkModel F then some ((incidenceList F).map (Solver.optimize F (initial F))) else none

/-- Return a satisfying finite occurrence buffer, rejecting both unsatisfiable instances and
instances outside the checked edge/even-delta-matroid model. -/
@[expose] def solve (F : CSP Table ℕ) : Option (List Bool) := do
  let bits ← optimize F
  if F.vars.any (EdgeAugmenting.inconsistent F bits) then none else some bits

/-- A total guarded SAT decision on raw binary-name, explicit-table CSPs. -/
@[expose] def decideSAT (F : CSP Table ℕ) : Bool := (solve F).isSome

/-- Every accepted optimizer output has exactly one bit per actual occurrence. -/
theorem optimize_width (F : CSP Table ℕ) {bits : List Bool} (h : optimize F = some bits) :
    bits.length = (incidenceList F).length := by
  unfold optimize at h
  split at h
  · cases Option.some.inj h
    exact List.length_map _
  · contradiction

/-- The optimizer returns an actual minimum over all valid original positional labelings. -/
theorem optimize_spec (F : CSP Table ℕ) (h : checkModel F = true) :
    ∃ bits, optimize F = some bits ∧
      IsOptimalLabeling Table.sem (EdgeAugmenting.labeling F bits) := by
  have hm := checkModel_sound F h
  refine ⟨(incidenceList F).map (Solver.optimize F (initial F)), ?_, ?_⟩
  · simp only [optimize, h, ↓reduceIte]
  · rw [EdgeAugmenting.labeling_map]
    exact Solver.optimize_spec F (initial F) hm.1 (initial_valid F h) hm.2

/-- The finite original-name consistency scan is exactly zero actual occurrence defects. -/
theorem no_inconsistent_iff (F : CSP Table ℕ) (bits : List Bool) :
    F.vars.any (EdgeAugmenting.inconsistent F bits) = false ↔
      (defects (EdgeAugmenting.labeling F bits)).card = 0 := by
  simp only [List.any_eq_false, EdgeAugmenting.inconsistent_eq, decide_eq_true_eq,
    Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem, mem_defects]
  constructor
  · intro h v hi
    have hv := hi
    obtain ⟨o, _, ho, _, _⟩ := hv
    exact h v (ho ▸ o.var_mem) hi
  · exact fun h v _ => h v

/-- Every returned optimizer buffer has actual width and is a minimum over all valid original
occurrence labelings. The complete model guard is derived from its successful return. -/
theorem optimize_result_spec (F : CSP Table ℕ) {bits : List Bool}
    (h : optimize F = some bits) : checkModel F = true ∧
      bits.length = (incidenceList F).length ∧
        IsOptimalLabeling Table.sem (EdgeAugmenting.labeling F bits) := by
  by_cases hm : checkModel F = true
  · obtain ⟨out, ho, hopt⟩ := optimize_spec F hm
    have he : out = bits := Option.some.inj (ho.symm.trans h)
    subst out
    exact ⟨hm, optimize_width F h, hopt⟩
  · simp only [optimize, hm, Bool.false_eq_true, ↓reduceIte] at h
    contradiction

/-- SAT correctness on the full raw input: acceptance is equivalent to passing the actual
finite model checks and satisfiability under `Table.sem`. No runtime assumption is supplied. -/
theorem decideSAT_eq_true (F : CSP Table ℕ) :
    decideSAT F = true ↔ checkModel F = true ∧ F.Satisfiable Table.sem := by
  by_cases hm : checkModel F = true
  · obtain ⟨bits, hb, ho⟩ := optimize_spec F hm
    have hz : (defects (EdgeAugmenting.labeling F bits)).card = 0 ↔
        F.Satisfiable Table.sem := by
      rw [satisfiable_iff_exists_zero_defects Table.sem]
      constructor
      · exact fun h => ⟨_, ho.1, h⟩
      · rintro ⟨g, hg, he⟩
        have := ho.2 g hg
        omega
    simp only [decideSAT, solve, hb, Option.bind_eq_bind, Option.bind_some]
    have hh := (no_inconsistent_iff F bits).trans hz
    cases he : F.vars.any (EdgeAugmenting.inconsistent F bits) with
    | false => simp [hm, hh.mp he]
    | true =>
      have hn : ¬ F.Satisfiable Table.sem := fun hs => Bool.noConfusion (he.symm.trans (hh.mpr hs))
      simp [hm, hn]
  · simp [decideSAT, solve, optimize, hm]

end Cslib.Complexity.CSP.EdgeSolver
