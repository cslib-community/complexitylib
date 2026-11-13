/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Ports
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Fin

/-!
# Concrete size decrease of whole-instance blossom contraction

For `b` distinct blossom variables and `r` distinct touched original constraints,
the constructor has `old.numVars - b + r` occurring variables and one additional positive-scope
constraint. Every touched constraint has at least two internal positions, so `r ≤ b`.
The natural resource `2 * numVars - positiveCount` strictly decreases even when `r = b`.
Nullary constraints are preserved but do not contribute to the positive count.

This is the finite accounting behind Observation 26 and Corollary 27 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 13. No native time bound is claimed.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Finset

variable {F : CSP Table ℕ} {w : Walk F}

/-- Gathering positions counts actual internal occurrences in the original scope. -/
theorem length_positions (vs scope : List ℕ) :
    (positions vs scope).length = (scope.filter fun v => vs.contains v).length := by
  have he := congrArg (fun xs : List ℕ => (xs.filter fun v => vs.contains v).length)
    (List.map_getD_range scope 0)
  simpa only [List.filter_map, List.length_map, Function.comp_def, positions] using he

/-- Every deleted name in the actual trail was an occurring original variable. -/
theorem internal_subset_vars (w : Walk F) : (internal w).toFinset ⊆ F.vars.toFinset := by
  intro v hv
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp (List.mem_toFinset.mp hv))
  exact List.mem_toFinset.mpr o.var_mem

/-- Summed internal position counts are funded by the original finite occurrence list. -/
theorem sum_length_positions (vs : List ℕ) :
    (∑ i : Fin F.length, (positions vs F[i.val].scope).length) =
      (F.vars.filter fun v => vs.contains v).length := by
  calc
    _ = (List.ofFn fun i : Fin F.length =>
        (F[i.val].scope.filter fun v => vs.contains v).length).sum := by
      simp only [List.sum_ofFn, length_positions]
    _ = (F.map fun c => (c.scope.filter fun v => vs.contains v).length).sum :=
      congrArg List.sum (List.ofFn_getElem_eq_map F
        (fun c => (c.scope.filter fun v => vs.contains v).length))
    _ = _ := by simp [vars, List.filter_flatMap, List.length_flatMap]

/-- An edge instance spends precisely two old ports per selected occurring variable. -/
theorem length_internal_occurrences (hF : EdgeInstance F) (vs : List ℕ)
    (hv : vs.toFinset ⊆ F.vars.toFinset) :
    (F.vars.filter fun v => vs.contains v).length = 2 * vs.toFinset.card := by
  have he : (F.vars.filter fun v => vs.contains v).toFinset = vs.toFinset := by
    ext v
    simp only [List.mem_toFinset, List.mem_filter, List.contains_iff_mem]
    constructor
    · exact And.right
    · intro hm
      exact ⟨List.mem_toFinset.mp (hv (List.mem_toFinset.mpr hm)), hm⟩
  rw [← List.sum_toFinset_count_eq_length, he]
  have hc : ∀ v ∈ vs.toFinset, (F.vars.filter fun v => vs.contains v).count v = 2 := by
    intro v hmem
    rw [List.count_filter (by simpa using hmem)]
    exact hF.count_vars (List.mem_toFinset.mp (hv hmem))
  calc
    _ = ∑ _v ∈ vs.toFinset, 2 := sum_congr rfl hc
    _ = _ := by simp [mul_comm]

/-- Two internal ports at every touched original constraint imply `r ≤ b`, even when copied
nodes of a repeated original constraint occur several times in the blossom. -/
theorem length_touched_le_internal (hF : EdgeInstance F) (hw : w.IsWalk)
    (hc : w.finish = w.start) : (touched F (internal w)).length ≤ (internal w).toFinset.card := by
  have hle : 2 * (touched F (internal w)).length ≤
      ∑ i : Fin F.length, (positions (internal w) F[i.val].scope).length := by
    calc
      _ = ∑ _i ∈ (touched F (internal w)).toFinset, 2 := by
        simp [List.toFinset_card_of_nodup (nodup_touched F (internal w)), mul_comm]
      _ ≤ ∑ i ∈ (touched F (internal w)).toFinset,
          (positions (internal w) F[i.val].scope).length :=
        sum_le_sum fun i hi => two_le_positions hF hw hc (List.mem_toFinset.mp hi)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
  rw [sum_length_positions, length_internal_occurrences hF _ (internal_subset_vars w)] at hle
  omega

/-- The exact constructor cannot increase the number of occurring variables. -/
theorem numVars_contract_le (hF : EdgeInstance F) (hw : w.IsWalk)
    (hc : w.finish = w.start) (f : OccurrenceLabeling F Bool) :
    (contract f (internal w)).numVars ≤ F.numVars := by
  have hn := numVars_contract_add f (internal w) (internal_subset_vars w)
  have hr := length_touched_le_internal hF hw hc
  omega

/-- The actual finite contraction strictly decreases the recursion resource, including the
case where the variable count is unchanged. Every hypothesis comes from the actual blossom. -/
theorem contractionMeasure_contract_lt (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom Table.sem f) :
    (contract f (internal w)).contractionMeasure < F.contractionMeasure := by
  have hn := numVars_contract_le hF hb.1 hb.2.1 f
  have hp := positiveCount_contract f (internal w) (touched_ne_nil w hb.2.2.1)
  have hbnd := (edge_contract hF f (internal w)).positiveCount_le
  unfold contractionMeasure
  omega

/-- The actual number of stored table rows grows by at most `r`. The central table has `r`
rows of width `r`; thus its new Boolean row data is quadratic in `r`, not linear in `r`.
Every old table retains at most its original number of rows, with original outside order. -/
theorem totalRows_contract_le (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    ((contract f vs).map fun c => c.rel.rows.length).sum ≤
      (F.map fun c => c.rel.rows.length).sum + (touched F vs).length := by
  simp only [contract, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Table.length_rows_exactlyOne, length_connectors, Nat.add_zero]
  apply Nat.add_le_add_right
  rw [List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ i : Fin F.length, F[i.val].rel.rows.length :=
      sum_le_sum (fun i _ => rows_constraint_le f vs i)
    _ = (List.ofFn fun i : Fin F.length => F[i.val].rel.rows.length).sum := by rw [List.sum_ofFn]
    _ = _ := congrArg List.sum (List.ofFn_getElem_eq_map F (fun c => c.rel.rows.length))

end Cslib.Logic.PL.CSP.Blossom
