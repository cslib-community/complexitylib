/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Growth

/-!
# Exhaustion of the actual positional frontier

The search of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, Algorithm 1
step 2 (printed p. 10), exhausts exactly when every incidence of every visited variable has
been used. This is a theorem about a fresh executable run, without a search-completeness
hypothesis. `Forest.Optimality` combines this coverage with even-delta-matroid exchange
and a counting argument to prove Lemma 45 for a fresh exhausted run.

## Main results

* `search_exhausted_frontier`: a fresh exhausted run has no unused incidence at a visited variable.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- Every port not yet used remains in the finite work list. Repeated labels and sparse labels
do not change this positional coverage property. -/
@[expose] def Covers (es : Log F) (remaining : List (Occurrence F)) : Prop :=
  ∀ o : Occurrence F, o ∉ es.used → o ∈ remaining

omit [DecidableEq V] in
/-- Coverage survives the exact erase-and-filter operation performed on continuation. -/
theorem Covers.next {es : Log F} {remaining : List (Occurrence F)}
    (hc : Covers es remaining) (e : Expansion F) :
    Covers (e :: es) ((remaining.erase e.input).filter
      fun a => decide (a ∉ Log.used (e :: es))) := by
  intro o ho
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa only [decide_eq_true_eq] using ho⟩
  have hne : o ≠ e.input := fun he => ho (he ▸ List.mem_cons_self)
  have hold : o ∉ es.used := fun hm =>
    ho (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
  exact (List.mem_erase_of_ne hne).mpr (hc o hold)

/-- A returned exhausted forest has no unused port at a visited variable, provided its
initial work list covered every unused port. No event or optimality property is assumed. -/
theorem run_exhausted_frontier (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (rs : List V) (es : Log F)
    (remaining : List (Occurrence F)) (hc : Covers es remaining)
    {out : Log F} (hr : run sem f rs es remaining = .exhausted out) :
    ∀ o : Occurrence F, out.Visited rs o.var → o ∈ out.used := by
  unfold run at hr
  split at hr
  next hn =>
    cases hr
    intro o hv
    by_contra hu
    have hnone := List.find?_eq_none.mp hn o (hc o hu)
    exact hnone (by simpa only [decide_eq_true_eq] using hv)
  next input hi =>
    split at hr
    next os o =>
      dsimp only at hr
      split at hr <;> cases hr
    next os hs =>
      exact run_exhausted_frontier sem f rs _ _ (hc.next _) hr
termination_by remaining.length
decreasing_by
  have hm : _ ∈ remaining := List.mem_of_find?_eq_some (by assumption)
  have hp : 0 < remaining.length := List.length_pos_of_mem hm
  apply Nat.lt_of_le_of_lt (List.length_filter_le _ _)
  rw [List.length_erase_of_mem hm]
  omega

/-- Fresh-run exhaustion of step 2, paid for by the actual incidence list. This does not
replace the separate optimality conclusion of source Lemma 45. -/
theorem search_exhausted_frontier (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) {out : Log F}
    (hr : search sem f = .exhausted out) :
    ∀ o : Occurrence F, out.Visited (roots f) o.var → o ∈ out.used :=
  run_exhausted_frontier sem f _ _ _ (fun o _ => mem_incidenceList o) hr

end Cslib.Logic.PL.CSP.Forest
