/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Forest.Trace

/-!
# Local growth certificates derived from executable partner scans

The certificates below record the actual step-2 choice and completed step-4 scan of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, Algorithm 1, printed p. 10.
They record local port conditions, not an assumed f-DAG or an optimality oracle.

## Main results

* `search_grown`: all completed expansions in a fresh executable search have local certificates.
* `Grown.outgoing_not_root`: discovered variables are not initial roots.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- Outputs accumulated before a scan continues or returns its first meeting. -/
@[expose] def ScanResult.outputs : ScanResult F → List (Occurrence F)
  | .continued os => os
  | .meeting os _ => os

/-- Every inserted child is fresh relative to the older forest, different from all other
inserted children, and an actual member of the candidate list or the initial output list. -/
theorem scan_outputs (rs : List V) (es : Log F) (input : Occurrence F)
    (bs os : List (Occurrence F))
    (hfresh : ∀ o ∈ os, ¬ es.Visited rs o.var)
    (hnodup : (os.map Occurrence.var).Nodup) :
    let out := (scan rs es input os bs).outputs
    (∀ o ∈ out, ¬ es.Visited rs o.var) ∧
      (out.map Occurrence.var).Nodup ∧ out ⊆ os ++ bs := by
  induction bs generalizing os with
  | nil => exact ⟨hfresh, hnodup, by simp [scan, ScanResult.outputs]⟩
  | cons b bs ih =>
    simp only [scan]
    split
    next hnew =>
      have hb : ¬ es.Visited rs b.var := fun hv => hnew (Or.imp_right
        (fun hm => List.mem_append_right _ hm) hv)
      have hbos : b.var ∉ os.map Occurrence.var := fun hm =>
        hnew (Or.inr (List.mem_append_left _ hm))
      have hf : ∀ o ∈ os ++ [b], ¬ es.Visited rs o.var := by
        intro o ho
        rcases List.mem_append.mp ho with ho | ho
        · exact hfresh o ho
        · exact List.mem_singleton.mp ho ▸ hb
      have hn : ((os ++ [b]).map Occurrence.var).Nodup := by
        rw [List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨hnodup, by simp, ?_⟩
        intro v hv w hw he
        have hwb : w = b.var := List.mem_singleton.mp hw
        exact hbos ((he.trans hwb) ▸ hv)
      obtain ⟨hf, hn, hs⟩ := ih (os ++ [b]) hf hn
      refine ⟨hf, hn, fun o ho => ?_⟩
      have hm := hs ho
      simpa only [List.append_assoc, List.singleton_append] using hm
    next =>
      split
      · obtain ⟨hf, hn, hs⟩ := ih os hfresh hnodup
        refine ⟨hf, hn, fun o ho => ?_⟩
        rcases List.mem_append.mp (hs ho) with ho | ho
        · exact List.mem_append_left _ ho
        · exact List.mem_append_right _ (List.mem_cons_of_mem b ho)
      · exact ⟨hfresh, hnodup, List.subset_append_left _ _⟩

/-- Every expansion can be justified by a previously grown forest, a genuinely unused input
at a visited variable, and the local facts proved by its scan. Saturation concerns every
feasible partner, including partners skipped because their parent has the same original
constraint at an older timestamp. -/
inductive Grown (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (rs : List V) : Log F → Prop where
  /-- Initial forest consists solely of isolated roots. -/
  | nil : Grown sem f rs []
  /-- A complete scan extends a previously grown forest. -/
  | cons {es : Log F} {e : Expansion F}
      (previous : Grown sem f rs es)
      (visited : es.Visited rs e.input.var)
      (unused : e.input ∉ es.used)
      (fresh : ∀ o ∈ e.outputs, ¬ es.Visited rs o.var)
      (distinct : (e.outputs.map Occurrence.var).Nodup)
      (feasible : ∀ o ∈ e.outputs, o ∈ partners sem f e.input)
      (saturated : ∀ o ∈ partners sem f e.input, o ∈ e.outputs ++ es.outgoing) :
      Grown sem f rs (e :: es)

/-- Every discovery variable is a nonroot, including across repeated constraint copies. -/
theorem Grown.outgoing_not_root {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {rs : List V} {es : Log F}
    (hg : Grown sem f rs es) {o : Occurrence F}
    (ho : o ∈ es.outgoing) : o.var ∉ rs := by
  induction hg with
  | nil => simp [Log.outgoing] at ho
  | @cons es e hp hv hu hf hn hfe hsat ih =>
    rcases List.mem_append.mp ho with ho | ho
    · exact fun hr => hf o ho (Or.inl hr)
    · exact ih ho

/-- A real continuing scan, together with the selected frontier incidence, supplies all local
conditions of a growth certificate. No forest/DAG correctness is assumed. -/
theorem Grown.of_scan {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    (hF : EdgeInstance F) {rs : List V} {es : Log F} (hg : Grown sem f rs es)
    {input : Occurrence F} (hv : es.Visited rs input.var) (hu : input ∉ es.used)
    {os : List (Occurrence F)} (hs : scan rs es input [] (partners sem f input) =
      .continued os) : Grown sem f rs (⟨input, os⟩ :: es) := by
  have h := scan_outputs rs es input (partners sem f input) [] (by simp) (by simp)
  rw [hs] at h
  refine .cons hg hv hu h.1 h.2.1 ?_ ?_
  · intro o ho
    exact h.2.2 ho
  · exact scan_saturated hF rs es input _ []
      (fun o ho => (mem_partners sem f input o).mp ho |>.1.symm) hs

namespace Log

/-- Any port already used by a grown forest belongs to a visited variable. -/
theorem Grown.used_visited {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {rs : List V} {es : Log F}
    (hg : Forest.Grown sem f rs es) {o : Occurrence F} (ho : o ∈ es.used) :
    es.Visited rs o.var := by
  induction hg with
  | nil => simp [used] at ho
  | @cons es e hp hv hu hf hn hfe hs ih =>
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hv.imp_right (fun hm => List.mem_append_right _ hm)
    · rcases List.mem_append.mp ho with ho | ho
      · exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))
      · exact (ih ho).imp_right (fun hm => List.mem_append_right _ hm)

/-- Every fresh output port is distinct from every older used port. -/
theorem Grown.output_not_used {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {rs : List V} {es : Log F}
    (hg : Forest.Grown sem f rs es) {os : List (Occurrence F)}
    (hf : ∀ o ∈ os, ¬ es.Visited rs o.var) {o : Occurrence F} (ho : o ∈ os) :
    o ∉ es.used := fun hu => hf o ho (Grown.used_visited hg hu)

/-- The two ports of an inserted step name distinct variables, even before invoking the
edge-instance hypothesis used elsewhere. -/
theorem Grown.output_var_ne {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {rs : List V} {es : Log F} {e : Expansion F}
    (hg : Forest.Grown sem f rs (e :: es)) {o : Occurrence F} (ho : o ∈ e.outputs) :
    e.input.var ≠ o.var := by
  cases hg with
  | cons _ hv _ hf =>
    intro he
    exact hf o ho (he ▸ hv)

end Log

/-- The predicate on all completed logs returned by a search; a meeting also has an older
completed log, while its current scan is deliberately partial. -/
@[expose] def Result.Logs (P : Log F → Prop) : Result F → Prop
  | .exhausted es => P es
  | .augment m => P m.older
  | .blossom m => P m.older

/-- Every completed expansion in the actual executable run has a local growth certificate.
The only recursive precondition is exact remaining-port freshness, supplied by the program's
filter and true initially. This theorem assumes neither DAG nor event correctness. -/
theorem run_grown (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (rs : List V) (es : Log F) (remaining : List (Occurrence F))
    (hg : Grown sem f rs es) (hu : ∀ o ∈ remaining, o ∉ es.used) :
    (run sem f rs es remaining).Logs (Grown sem f rs) := by
  unfold run
  split
  · exact hg
  next input hi =>
    have hv : es.Visited rs input.var := by
      simpa only [decide_eq_true_eq] using List.find?_some hi
    have huinput := hu input (List.mem_of_find?_eq_some hi)
    split
    next os o =>
      dsimp only
      split <;> exact hg
    next os hs =>
      apply run_grown sem f hF rs _ _ (hg.of_scan hF hv huinput hs)
      intro o ho
      exact of_decide_eq_true (List.mem_filter.mp ho).2
termination_by remaining.length
decreasing_by
  rename_i input _hi _ _ os _ _
  have hm : input ∈ remaining := List.mem_of_find?_eq_some _hi
  have hpos : 0 < remaining.length := List.length_pos_of_mem hm
  have he := List.length_erase_of_mem hm
  have hf := List.length_filter_le (fun a => decide
    (a ∉ Log.used ((⟨input, os⟩ : Expansion F) :: es))) (remaining.erase input)
  omega

/-- Every completed log in a fresh search is derived from actual frontier choices and scans. -/
theorem search_grown (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) : (search sem f).Logs (Grown sem f (roots f)) :=
  run_grown sem f hF _ _ _ .nil (by simp [Log.used])

end Cslib.Logic.PL.CSP.Forest
