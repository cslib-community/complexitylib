/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Complexity.Foundations.Data.List.Blocks
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite size accounting for edge CSPs

Every edge variable has two positional occurrences. Positive-scope constraints are therefore
bounded by twice the number of occurring variables. Nullary constraints are retained in the
instance but excluded from this count, as required for the recursion argument in Corollary 27
of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 13.
-/

public section

namespace Cslib.Logic.PL.CSP

open Finset

variable {Rel V : Type*} [DecidableEq V] {F : CSP Rel V}

/-- Constraints with positive scope, retaining positional multiplicity. -/
@[expose] def positiveCount (F : CSP Rel V) : ℕ :=
  (F.filter fun c => !c.2.isEmpty).length

omit [DecidableEq V] in
/-- The number of positions is the cardinality of the original dependent occurrence type. -/
theorem card_occurrence (F : CSP Rel V) : Fintype.card (Occurrence F) = F.vars.length := by
  calc
    Fintype.card (Occurrence F) = ∑ i : Fin F.length, F[i.val].2.length := by
      simp [Occurrence, Fintype.card_sigma]
    _ = (List.ofFn fun i : Fin F.length => F[i.val].2.length).sum := by
      rw [List.sum_ofFn]
    _ = (F.map fun c => c.2.length).sum := by
      exact congrArg List.sum (List.ofFn_getElem_eq_map F (fun c => c.2.length))
    _ = F.vars.length := by simp [vars, List.length_flatMap]

/-- Counting a variable in the occurrence list counts its actual positional fiber. -/
theorem card_occurrences_var (F : CSP Rel V) (v : V) :
    ((univ : Finset (Occurrence F)).filter fun o => o.var = v).card = F.vars.count v := by
  have hlocal (scope : List V) :
      (∑ j : Fin scope.length, if scope[j.val] = v then 1 else 0) = scope.count v := by
    have he : (List.ofFn fun j : Fin scope.length => scope[j.val]) = scope := by
      simp
    have hc := List.countP_ofFn (fun j : Fin scope.length => scope[j.val]) (fun w => w == v)
    simpa only [he, List.count_eq_countP, beq_iff_eq] using hc.symm
  calc
    _ = ∑ o : Occurrence F, if o.var = v then 1 else 0 := by simp
    _ = ∑ i : Fin F.length, ∑ j : Fin F[i.val].2.length,
        if F[i.val].2[j.val] = v then 1 else 0 := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ i : Fin F.length, F[i.val].2.count v := sum_congr rfl (fun i _ => hlocal _)
    _ = F.vars.count v := by
      rw [vars, List.count_flatMap]
      simp only [Function.comp_def]
      rw [← List.ofFn_getElem_eq_map F (fun c => c.2.count v), List.sum_ofFn]

/-- The two endpoints are exactly the finite fiber over an occurring edge variable. -/
theorem EdgeInstance.card_occurrences_var (hF : EdgeInstance F) (v : V)
    (hv : v ∈ F.vars.toFinset) :
    ((univ : Finset (Occurrence F)).filter fun o => o.var = v).card = 2 := by
  obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hv)
  have he : ((univ : Finset (Occurrence F)).filter fun p => p.var = o.var) =
      {o, hF.partner o} := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · exact hF.eq_or_eq_partner
    · rintro (rfl | rfl)
      · rfl
      · exact (hF.partner_variable o).symm
  rw [he]
  simp [hF.partner_ne o]

/-- Every occurring edge variable appears exactly twice in the original occurrence list. -/
theorem EdgeInstance.count_vars (hF : EdgeInstance F) {v : V} (hv : v ∈ F.vars) :
    F.vars.count v = 2 := by
  rw [← Cslib.Logic.PL.CSP.card_occurrences_var F v]
  exact hF.card_occurrences_var v (List.mem_toFinset.mpr hv)

omit [DecidableEq V] in
/-- Every actual scope of an edge instance has distinct variable names. -/
theorem EdgeInstance.scope_nodup (hF : EdgeInstance F) (i : Fin F.length) :
    F[i.val].2.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro j k he
  have hp : (⟨i, j⟩ : Occurrence F) = ⟨i, k⟩ := hF.eq_of_constraint_eq he rfl
  exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2

/-- Distinct scope names and exactly two occurrences characterize an edge instance.
The count ranges over the actual finite occurrence list, not a declared variable universe. -/
theorem edgeInstance_of_count_vars
    (hs : ∀ i : Fin F.length, F[i.val].2.Nodup)
    (hc : ∀ v ∈ F.vars, F.vars.count v = 2) : EdgeInstance F := by
  have hinj : ∀ o p : Occurrence F, o.var = p.var → o.1 = p.1 → o = p := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hv hi
    dsimp only at hi
    subst k
    have he : j = l := (hs i).injective_get hv
    subst l
    rfl
  intro o
  let s := (univ : Finset (Occurrence F)).filter fun p => p.var = o.var
  have hcard : s.card = 2 := (card_occurrences_var F o.var).trans (hc _ o.var_mem)
  obtain ⟨a, b, hab, he⟩ := card_eq_two.mp hcard
  have hmem : ∀ p : Occurrence F, p ∈ s ↔ p.var = o.var := by simp [s]
  have ho : o ∈ s := hmem o |>.mpr rfl
  rw [he] at ho
  have hcases : ∀ p : Occurrence F, p.var = o.var → p = a ∨ p = b := by
    intro p hp
    have hm := (hmem p).mpr hp
    simpa only [he, mem_insert, mem_singleton] using hm
  have ha : a.var = o.var := (hmem a).mp (he ▸ mem_insert_self a {b})
  have hb : b.var = o.var := (hmem b).mp (he ▸ mem_insert_of_mem (mem_singleton_self b))
  rcases mem_insert.mp ho with rfl | ho
  · refine ⟨b, ?_, hb.symm, fun p hp => hcases p hp⟩
    exact fun hi => hab (hinj o b hb.symm hi)
  · have hob := mem_singleton.mp ho
    subst o
    refine ⟨a, ?_, ha.symm, fun p hp => (hcases p hp).symm⟩
    exact fun hi => hab (hinj a b ha hi.symm)

/-- Exactly two occurrences per occurring variable, without a finite ambient universe. -/
theorem EdgeInstance.length_vars_eq_two_mul_numVars (hF : EdgeInstance F) :
    F.vars.length = 2 * F.numVars := by
  rw [← card_occurrence]
  calc
    Fintype.card (Occurrence F) = (univ : Finset (Occurrence F)).card := by simp
    _ = ∑ v ∈ F.vars.toFinset,
        ((univ : Finset (Occurrence F)).filter fun o => o.var = v).card :=
      card_eq_sum_card_fiberwise (fun a _ => List.mem_toFinset.mpr a.var_mem)
    _ = ∑ _v ∈ F.vars.toFinset, 2 := sum_congr rfl hF.card_occurrences_var
    _ = 2 * F.numVars := by simp [numVars, mul_comm]

omit [DecidableEq V] in
/-- Every positive-scope constraint spends at least one actual positional occurrence. -/
theorem positiveCount_le_length_vars (F : CSP Rel V) : F.positiveCount ≤ F.vars.length := by
  induction F with
  | nil => simp [positiveCount, vars]
  | cons c F ih =>
    by_cases he : c.2 = []
    · simpa [positiveCount, vars, he] using ih
    · have hp := List.length_pos_iff.mpr he
      simp only [positiveCount, List.filter_cons, vars, List.flatMap_cons,
        List.length_append] at ih ⊢
      simp only [List.isEmpty_eq_false_iff.mpr he, Bool.not_false, ite_true, List.length_cons]
      omega

/-- The positive constraint count is bounded even when nullary constraints are present. -/
theorem EdgeInstance.positiveCount_le (hF : EdgeInstance F) : F.positiveCount ≤ 2 * F.numVars :=
  (positiveCount_le_length_vars F).trans_eq hF.length_vars_eq_two_mul_numVars

/-- The finite recursion resource counts occurring variables and positive-scope constraints. -/
@[expose] def contractionMeasure (F : CSP Rel V) : ℕ := 2 * F.numVars - F.positiveCount

end Cslib.Logic.PL.CSP
