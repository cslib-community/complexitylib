/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Subpath

/-!
# First entry of an incidence walk into a finite variable set

The first boundary index scans actual step outputs. Linkage proves that all preceding ports
are outside and that the first internal port is an output. Variable names are compared as data;
no integer interval below their binary values is enumerated.
-/

public section

namespace Cslib.Logic.PL.CSP.Walk

variable {Rel V : Type*} {F : CSP Rel V}

/-- A linked walk preserves a variable property at all ports when its start and every step
output have that property. -/
theorem Linked.forall_ports {P : V → Prop} {v : V}
    {ss : List (Occurrence F × Occurrence F)} (hl : Linked v ss) (hv : P v)
    (houtputs : ∀ s ∈ ss, P s.2.var) : ∀ o ∈ edgesOf ss, P o.var := by
  induction ss generalizing v with
  | nil => simp [edgesOf]
  | cons s ss ih =>
    intro o ho
    change o ∈ s.1 :: s.2 :: edgesOf ss at ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hl.1 ▸ hv
    · rcases List.mem_cons.mp ho with rfl | ho
      · exact houtputs s List.mem_cons_self
      · exact ih hl.2.2 (houtputs s List.mem_cons_self)
          (fun t ht => houtputs t (List.mem_cons_of_mem s ht)) o ho

/-- The last variable has every property shared by the start and all actual used ports. -/
theorem finish_property (w : Walk F) {P : V → Prop} (hs : P w.start)
    (hp : ∀ o ∈ w.edges, P o.var) : P w.finish := by
  by_cases hn : w.steps = []
  · simpa only [finish, hn, finishFrom] using hs
  · obtain ⟨s, hsm, he⟩ := finish_step w hn
    exact he ▸ hp s.2 (List.mem_flatMap.mpr ⟨s, hsm, by simp⟩)

/-- The next actual input names the final variable of its preceding whole-step prefix. -/
theorem IsWalk.input_eq_finish_take {w : Walk F} (hw : w.IsWalk)
    (j : ℕ) (hj : j < w.steps.length) : w.steps[j].1.var = (w.take j).finish := by
  have hl := (hw.drop j).1
  change Linked (w.take j).finish (w.steps.drop j) at hl
  rw [List.drop_eq_getElem_cons hj] at hl
  exact hl.1

/-- The first step whose output names a selected variable; length means no such step. -/
@[expose] def boundaryIndex [DecidableEq V] (w : Walk F) (vs : List V) : ℕ :=
  w.steps.findIdx fun (_, output) => vs.contains output.var

/-- First-entry scan correctness, including avoidance by every earlier actual incidence. -/
theorem boundaryIndex_spec [DecidableEq V] {w : Walk F} (hw : w.IsWalk) (vs : List V)
    (hstart : w.start ∉ vs) (hex : ∃ o ∈ w.edges, o.var ∈ vs) :
    ∃ hk : boundaryIndex w vs < w.steps.length,
      w.steps[boundaryIndex w vs].2.var ∈ vs ∧
        ∀ o ∈ (w.take (boundaryIndex w vs)).edges, o.var ∉ vs := by
  have hsome : ∃ s ∈ w.steps, vs.contains s.2.var = true := by
    by_contra hn
    have hout : ∀ s ∈ w.steps, s.2.var ∉ vs := by
      intro s hs hv
      exact hn ⟨s, hs, List.contains_iff_mem.mpr hv⟩
    obtain ⟨o, ho, hv⟩ := hex
    exact hw.1.forall_ports (P := fun v => v ∉ vs) hstart hout o ho hv
  have hk : boundaryIndex w vs < w.steps.length := List.findIdx_lt_length.mpr hsome
  have hin : w.steps[boundaryIndex w vs].2.var ∈ vs := by
    apply List.contains_iff_mem.mp
    exact List.findIdx_getElem
      (p := fun s : Occurrence F × Occurrence F => vs.contains s.2.var) (w := hk)
  refine ⟨hk, hin, (hw.take (boundaryIndex w vs)).1.forall_ports
    (P := fun v => v ∉ vs) hstart ?_⟩
  intro s hs
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hs
  have hjk : j < boundaryIndex w vs := by
    have hh := List.length_take_le (boundaryIndex w vs) w.steps
    exact lt_of_lt_of_le hj hh
  have hh := List.not_of_lt_findIdx
    (p := fun s : Occurrence F × Occurrence F => vs.contains s.2.var) hjk
  simp only [take, List.getElem_take] at he
  rw [he] at hh
  simpa using hh

end Cslib.Logic.PL.CSP.Walk
