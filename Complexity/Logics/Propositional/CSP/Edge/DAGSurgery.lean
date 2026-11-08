/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.DAG
import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations
import Complexity.Logics.Propositional.CSP.Edge.Walk.Operations

/-!
# Surgery on timestamped edge-CSP DAGs

This formalizes Lemmas 35 and 37, Corollary 36's graph argument, and Lemma 43 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 16–20. The four-coordinate
exchange consequences are applied to actual positional tuples to prove preservation of both
local feasibility and the full no-shortcut invariant. Common local parity may be odd.

`delete_earliest_pair` has the source's exact leaf and degree hypotheses and identifies the
removed arcs. `removeRootCopy` and `removeCopy` prove stronger deletion variants that retain
isolated supported nodes as appropriate. `reroot_earliest` retains every unselected outgoing
child and proves the changed topological order, moving the selected variable before all others.

`valid_flip_of_pairedCopies` proves a stronger form of Corollary 36 by induction on constraint
copies: every copy has precisely two incident arcs, at least one incoming. The path-to-`Walk`
bridges are in `DAGPaths`. Nothing excludes revisits of an original constraint at different times.

`flip_walk_of_no_prefix_extension` is Lemma 43 with actual `Walk.take`/`snoc` hypotheses.
Its proof is an alternative to the paper's temporary earlier timestamp: direct exchange gives
`external_pair`, which is iterated over all variable-ended prefixes. Thus no assumption that a
smaller natural timestamp exists is needed, including when a current timestamp is zero.

The local surgery arguments in fact hold for arbitrary occurrence-indexed CSP lists; an
`EdgeInstance` identifies this positional extension with the source's no-repeat edge model.
No surgery conclusion, path validity, comparison labeling, forest construction or solver is
included among the six invariant assumptions. Algorithm 1 and its Lemma 34 are separate work.

## Main results

* `IsFDAG.delete_earliest_pair`: Lemma 35, including exact removal of the two displayed arcs.
* `IsFDAG.reroot_earliest`: Lemma 37, retaining other children.
* `IsFDAG.valid_flip_of_pairedCopies`: the graph form of Corollary 36.
* `IsFDAG.flip_walk_of_no_prefix_extension`: Lemma 43 on actual positional walks.
-/

public section

namespace Cslib.Logic.PL.CSP.DAG

open BitString Finset

variable {Rel V : Type*} {F : CSP Rel V}

/-- Cancelling pairs are symmetric, including equal occurrences. -/
theorem pairFlip_comm (f : OccurrenceLabeling F Bool) (a b : Occurrence F) :
    pairFlip f a b = pairFlip f b a := by
  funext q
  by_cases ha : q = a <;> by_cases hb : q = b <;> simp_all [pairFlip, flipOn_apply]

/-- Two pair moves sharing their middle occurrence cancel that occurrence. -/
theorem pairFlip_cancel (f : OccurrenceLabeling F Bool) (a b c : Occurrence F) :
    pairFlip (pairFlip f a b) b c = pairFlip f a c := by
  funext q
  by_cases ha : q = a <;> by_cases hb : q = b <;>
    by_cases hc : q = c <;> simp [pairFlip, flipOn_apply, ha, hb, hc]

private theorem pairFlip_at_other (f : OccurrenceLabeling F Bool) {a b q : Occurrence F}
    (ha : q.1 ≠ a.1) (hb : q.1 ≠ b.1) : pairFlip f a b q = f q := by
  have hqa : q ≠ a := fun h => ha (congrArg Sigma.fst h)
  have hqb : q ≠ b := fun h => hb (congrArg Sigma.fst h)
  simp [pairFlip, flipOn_apply, hqa, hqb]

private theorem localTuple_pairFlip (f : OccurrenceLabeling F Bool) (i : Fin F.length)
    (a b : Fin F[i].2.length) (hab : a ≠ b) :
    localTuple (pairFlip f ⟨i, a⟩ ⟨i, b⟩) i =
      List.ofFn (flipOn {a, b} (fun j => f ⟨i, j⟩)) := by
  rw [pairFlip_eq f (sigma_mk_injective.ne hab)]
  apply congrArg List.ofFn
  funext j
  simp [flipOn_apply]

/-- Feasibility of a two-port move is exactly local feasibility at its positional constraint. -/
theorem validLabeling_pairFlip_iff {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (i : Fin F.length) (a b : Fin F[i].2.length) (hab : a ≠ b) :
    ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, b⟩) ↔
      sem F[i].1 (List.ofFn (flipOn {a, b} (fun j => f ⟨i, j⟩))) = true := by
  constructor
  · intro hv
    have h := hv i
    rwa [localTuple_pairFlip f i a b hab] at h
  · intro hv
    rw [pairFlip_eq f (sigma_mk_injective.ne hab)]
    exact EdgeInstance.validLabeling_flipOn_pair hf i a b hv

private theorem four_eq (f : OccurrenceLabeling F Bool) (i : Fin F.length)
    {a b c d : Fin F[i].2.length}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    flipOn {c, d} (fun j => pairFlip f ⟨i, a⟩ ⟨i, b⟩ ⟨i, j⟩) =
      flipOn {a, b, c, d} (fun j => f ⟨i, j⟩) := by
  funext j
  by_cases ha : j = a <;> by_cases hb : j = b <;>
    by_cases hc : j = c <;> by_cases hd : j = d <;>
    simp_all [pairFlip, flipOn_apply]

/-- The substantive property-(5) transfer in KKR Lemmas 35 and 37.
The two forbidden old-incoming cross-pairs force the four-coordinate move. -/
theorem valid_pairFlip_pairFlip_of_no_cross {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (i : Fin F.length) {a b c d : Fin F[i].2.length}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habf : ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, b⟩))
    (hcdf : ValidLabeling sem (pairFlip f ⟨i, c⟩ ⟨i, d⟩))
    (hacf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, c⟩))
    (hadf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, d⟩)) :
    ValidLabeling sem (pairFlip (pairFlip f ⟨i, a⟩ ⟨i, b⟩) ⟨i, c⟩ ⟨i, d⟩) := by
  apply (validLabeling_pairFlip_iff habf i c d hcd).mpr
  rw [four_eq f i hab hac had hbc hbd hcd]
  exact (hM i).mem_flipOn_four_of_not_mem_cross hab hac had hbc hbd hcd
    ((validLabeling_pairFlip_iff hf i a b hab).mp habf)
    ((validLabeling_pairFlip_iff hf i c d hcd).mp hcdf)
    (fun h => hacf ((validLabeling_pairFlip_iff hf i a c hac).mpr h))
    (fun h => hadf ((validLabeling_pairFlip_iff hf i a d had).mpr h))

/-- The substantive no-shortcut transfer in KKR Lemmas 35 and 37.
Exchange toward the feasible base would produce one of three forbidden pairs. -/
theorem not_valid_pairFlip_pairFlip_of_no_cross {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (i : Fin F.length) {a b c d : Fin F[i].2.length}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habf : ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, b⟩))
    (hcdf : ¬ ValidLabeling sem (pairFlip f ⟨i, c⟩ ⟨i, d⟩))
    (hacf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, c⟩))
    (hadf : ¬ ValidLabeling sem (pairFlip f ⟨i, a⟩ ⟨i, d⟩)) :
    ¬ ValidLabeling sem (pairFlip (pairFlip f ⟨i, a⟩ ⟨i, b⟩) ⟨i, c⟩ ⟨i, d⟩) := by
  intro h
  have hfour := (validLabeling_pairFlip_iff habf i c d hcd).mp h
  rw [four_eq f i hab hac had hbc hbd hcd] at hfour
  rcases (hM i).mem_pair_or_mem_cross_of_mem_flipOn_four hab hac had hbc hbd hcd
      (hf i) hfour with h | h | h
  · exact hcdf ((validLabeling_pairFlip_iff hf i c d hcd).mpr h)
  · exact hacf ((validLabeling_pairFlip_iff hf i a c hac).mpr h)
  · exact hadf ((validLabeling_pairFlip_iff hf i a d had).mpr h)

private theorem valid_four_occurrences {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) {a b c d : Occurrence F}
    (hiab : a.1 = b.1) (hiac : a.1 = c.1) (hiad : a.1 = d.1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habf : ValidLabeling sem (pairFlip f a b))
    (hcdf : ValidLabeling sem (pairFlip f c d))
    (hacf : ¬ ValidLabeling sem (pairFlip f a c))
    (hadf : ¬ ValidLabeling sem (pairFlip f a d)) :
    ValidLabeling sem (pairFlip (pairFlip f a b) c d) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases c with ⟨k, c⟩
  rcases d with ⟨l, d⟩
  dsimp only at hiab hiac hiad
  subst j; subst k; subst l
  exact valid_pairFlip_pairFlip_of_no_cross hM hf i
    (fun h => hab (h ▸ rfl)) (fun h => hac (h ▸ rfl)) (fun h => had (h ▸ rfl))
    (fun h => hbc (h ▸ rfl)) (fun h => hbd (h ▸ rfl)) (fun h => hcd (h ▸ rfl))
    habf hcdf hacf hadf

private theorem not_valid_four_occurrences {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) {a b c d : Occurrence F}
    (hiab : a.1 = b.1) (hiac : a.1 = c.1) (hiad : a.1 = d.1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habf : ValidLabeling sem (pairFlip f a b))
    (hcdf : ¬ ValidLabeling sem (pairFlip f c d))
    (hacf : ¬ ValidLabeling sem (pairFlip f a c))
    (hadf : ¬ ValidLabeling sem (pairFlip f a d)) :
    ¬ ValidLabeling sem (pairFlip (pairFlip f a b) c d) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases c with ⟨k, c⟩
  rcases d with ⟨l, d⟩
  dsimp only at hiab hiac hiad
  subst j; subst k; subst l
  exact not_valid_pairFlip_pairFlip_of_no_cross hM hf i
    (fun h => hab (h ▸ rfl)) (fun h => hac (h ▸ rfl)) (fun h => had (h ▸ rfl))
    (fun h => hbc (h ▸ rfl)) (fun h => hbd (h ▸ rfl)) (fun h => hcd (h ▸ rfl))
    habf hcdf hacf hadf

private theorem valid_pairFlip_other_iff {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f) {a b c d : Occurrence F}
    (hiab : a.1 = b.1) (hicd : c.1 = d.1) (hic : c.1 ≠ a.1)
    (hv : ValidLabeling sem (pairFlip f a b)) :
    ValidLabeling sem (pairFlip (pairFlip f a b) c d) ↔
      ValidLabeling sem (pairFlip f c d) := by
  by_cases hcd : c = d
  · subst d
    simp only [pairFlip_self]
    exact iff_of_true hv hf
  rcases c with ⟨i, c⟩
  rcases d with ⟨j, d⟩
  dsimp only at hicd hic
  subst j
  have hne : c ≠ d := fun h => hcd (h ▸ rfl)
  rw [validLabeling_pairFlip_iff hv i c d hne,
    validLabeling_pairFlip_iff hf i c d hne]
  have he : (fun j => pairFlip f a b ⟨i, j⟩) = (fun j => f ⟨i, j⟩) := by
    funext j
    exact pairFlip_at_other f hic (hiab ▸ hic)
  exact Iff.of_eq (congrArg
    (fun bits => sem F[i].1 (List.ofFn (flipOn {c, d} bits)) = true) he)

variable {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {T : DAG F}

/-- Different timestamps cannot reuse an original incidence. -/
theorem IsFDAG.occurrence_ne_of_time_ne (h : T.IsFDAG sem f) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (ht : a.time ≠ b.time) :
    a.occurrence ≠ b.occurrence :=
  fun he => ht (congrArg Arc.time (h.unique a ha b hb he))

/-- Opposite orientations cannot reuse an original incidence. -/
theorem IsFDAG.occurrence_ne_of_orientation_ne (h : T.IsFDAG sem f) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (ht : a.incoming ≠ b.incoming) :
    a.occurrence ≠ b.occurrence :=
  fun he => ht (congrArg Arc.incoming (h.unique a ha b hb he))

/-- Local feasibility at a later copy survives the earliest two-port move.
All original-constraint revisits are retained; the four-coordinate exchange handles them. -/
theorem IsFDAG.feasible_after_earlier (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b x y : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hx : x ∈ T.arcs) (hy : y ∈ T.arcs)
    (hai : a.incoming = true) (hne : a.occurrence ≠ b.occurrence) (hab : a.copy = b.copy)
    (hxi : x.incoming = true) (hxy : x.copy = y.copy) (ht : a.time < x.time) :
    ValidLabeling sem (pairFlip (pairFlip f a.occurrence b.occurrence)
      x.occurrence y.occurrence) := by
  have hv := h.feasible a ha b hb hai hab
  by_cases he : x.occurrence = y.occurrence
  · rw [he, pairFlip_self]
    exact hv
  have hbt : a.time = b.time := congrArg Prod.snd hab
  have hyt : x.time = y.time := congrArg Prod.snd hxy
  by_cases hc : x.occurrence.1 = a.occurrence.1
  · have hac := h.occurrence_ne_of_time_ne ha hx (by omega)
    have had := h.occurrence_ne_of_time_ne ha hy (by omega)
    have hbc := h.occurrence_ne_of_time_ne hb hx (by omega)
    have hbd := h.occurrence_ne_of_time_ne hb hy (by omega)
    exact valid_four_occurrences hM h.valid (congrArg Prod.fst hab) hc.symm
      (hc.symm.trans (congrArg Prod.fst hxy))
      hne hac had hbc hbd he
      hv (h.feasible x hx y hy hxi hxy)
      (h.noShortcut a ha x hx hai hc.symm ht)
      (h.noShortcut a ha y hy hai (hc.symm.trans (congrArg Prod.fst hxy)) (by omega))
  · exact (valid_pairFlip_other_iff h.valid (congrArg Prod.fst hab)
      (congrArg Prod.fst hxy) hc hv).mpr (h.feasible x hx y hy hxi hxy)

/-- The no-shortcut prohibition between later copies survives the earliest two-port move. -/
theorem IsFDAG.noShortcut_after_earlier (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b x y : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hx : x ∈ T.arcs) (hy : y ∈ T.arcs)
    (hai : a.incoming = true) (hne : a.occurrence ≠ b.occurrence) (hab : a.copy = b.copy)
    (hxi : x.incoming = true) (hxy : x.occurrence.1 = y.occurrence.1)
    (ht : a.time < x.time) (hxytime : x.time < y.time) :
    ¬ ValidLabeling sem (pairFlip (pairFlip f a.occurrence b.occurrence)
      x.occurrence y.occurrence) := by
  have hv := h.feasible a ha b hb hai hab
  have hbt : a.time = b.time := congrArg Prod.snd hab
  by_cases hc : x.occurrence.1 = a.occurrence.1
  · exact not_valid_four_occurrences hM h.valid (congrArg Prod.fst hab) hc.symm
      (hc.symm.trans hxy)
      hne
      (h.occurrence_ne_of_time_ne ha hx (by omega))
      (h.occurrence_ne_of_time_ne ha hy (by omega))
      (h.occurrence_ne_of_time_ne hb hx (by omega))
      (h.occurrence_ne_of_time_ne hb hy (by omega))
      (h.occurrence_ne_of_time_ne hx hy (by omega)) hv
      (h.noShortcut x hx y hy hxi hxy hxytime)
      (h.noShortcut a ha x hx hai hc.symm ht)
      (h.noShortcut a ha y hy hai (hc.symm.trans hxy) (by omega))
  · intro hn
    exact h.noShortcut x hx y hy hxi hxy hxytime
      ((valid_pairFlip_other_iff h.valid (congrArg Prod.fst hab) hxy hc hv).mp hn)

/-- A supported copy has minimum timestamp, including among isolated constraint copies. -/
@[expose] def Earliest (T : DAG F) (c : Copy F) : Prop :=
  c ∈ T.copies ∧ ∀ d ∈ T.copies, c.2 ≤ d.2

/-- A different copy is strictly later than a minimum copy: timestamps are globally unique. -/
theorem IsFDAG.time_lt_of_earliest (h : T.IsFDAG sem f) {c : Copy F}
    (hc : T.Earliest c) {a : Arc F} (ha : a ∈ T.arcs) (hne : a.copy ≠ c) :
    c.2 < a.time := by
  have ham := (h.supported a ha).2
  have hle := hc.2 a.copy ham
  have hne' : c.2 ≠ a.time := by
    intro he
    exact hne (h.ordered.1 a.copy ham c hc.1 he.symm)
  exact lt_of_le_of_ne hle hne'

section Surgery

variable [DecidableEq V]

/-- Reverse one indexed incidence without changing its original port or timestamp. -/
@[expose] def Arc.reverse (a : Arc F) : Arc F :=
  ⟨a.occurrence, a.time, !a.incoming⟩

/-- Delete the old root arc and reverse one selected child arc, retaining all other children. -/
@[expose] def reroot (T : DAG F) (a b : Arc F) : DAG F where
  vars := T.vars.erase a.occurrence.var
  copies := T.copies
  arcs := insert b.reverse (T.arcs.filter fun e => e ≠ a ∧ e ≠ b)

/-- The new root arc is distinguished from the unchanged, retained old arcs. -/
theorem mem_reroot_arcs {a b e : Arc F} :
    e ∈ (T.reroot a b).arcs ↔ e = b.reverse ∨ e ∈ T.arcs ∧ e ≠ a ∧ e ≠ b := by
  change e ∈ insert b.reverse (T.arcs.filter _) ↔ _
  simp only [mem_insert, mem_filter]

/-- Delete a variable root and a constraint copy, retaining all other supported nodes. -/
@[expose] def removeRootCopy (T : DAG F) (u : V) (c : Copy F) : DAG F :=
  T.restrict (T.vars.erase u) (T.copies.erase c)

/-- Earliest-copy deletion preserves the full f-DAG invariant after its two-port move.
This stronger form deletes every incident arc at the selected root and copy; the degree
hypotheses in Lemma 35 identify these with precisely its two displayed arcs. -/
theorem IsFDAG.removeRootCopy (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs)
    (hai : a.incoming = true) (hbo : b.incoming = false) (hab : a.copy = b.copy)
    (he : T.Earliest a.copy) :
    (T.removeRootCopy a.occurrence.var a.copy).IsFDAG sem
      (pairFlip f a.occurrence b.occurrence) := by
  have hs := h.restrict (T.vars.erase a.occurrence.var) (T.copies.erase a.copy)
  refine ⟨h.feasible a ha b hb hai hab, hs.supported, hs.unique, hs.indegree,
    hs.ordered, ?_, ?_⟩
  · intro x hx y hy hxi hxy
    obtain ⟨hxt, _, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyt, _, _⟩ := mem_filter.mp hy
    exact h.feasible_after_earlier hM ha hb hxt hyt hai
      (h.occurrence_ne_of_orientation_ne ha hb (by simp [hai, hbo])) hab hxi hxy
      (h.time_lt_of_earliest he hxt (mem_erase.mp hxc).1)
  · intro x hx y hy hxi hxy ht
    obtain ⟨hxt, _, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyt, _, _⟩ := mem_filter.mp hy
    exact h.noShortcut_after_earlier hM ha hb hxt hyt hai
      (h.occurrence_ne_of_orientation_ne ha hb (by simp [hai, hbo])) hab hxi hxy
      (h.time_lt_of_earliest he hxt (mem_erase.mp hxc).1) ht

/-- Lemma 35, KKR v6, printed pp. 16–17: flip `u C v`, remove `u,C^s` and exactly
the two displayed arcs. Both local feasibility and no shortcuts are proved by even exchange. -/
theorem IsFDAG.delete_earliest_pair (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs)
    (hai : a.incoming = true) (hbo : b.incoming = false) (hab : a.copy = b.copy)
    (he : T.Earliest a.copy)
    (hleaf : ∀ e ∈ T.arcs, e.occurrence.var = a.occurrence.var → e = a)
    (hdegree : ∀ e ∈ T.arcs, e.copy = a.copy → e = a ∨ e = b) :
    ValidLabeling sem (pairFlip f a.occurrence b.occurrence) ∧
      (T.removeRootCopy a.occurrence.var a.copy).IsFDAG sem
        (pairFlip f a.occurrence b.occurrence) ∧
      (T.removeRootCopy a.occurrence.var a.copy).arcs = (T.arcs.erase a).erase b := by
  refine ⟨h.feasible a ha b hb hai hab, h.removeRootCopy hM ha hb hai hbo hab he, ?_⟩
  apply Finset.ext
  intro e
  change e ∈ T.arcs.filter (fun z => z.occurrence.var ∈ T.vars.erase a.occurrence.var ∧
    z.copy ∈ T.copies.erase a.copy) ↔ e ∈ (T.arcs.erase a).erase b
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨het, ⟨hvar, _⟩, hcopy, _⟩
    refine ⟨?_, ?_, het⟩
    · intro he
      subst e
      exact hcopy hab.symm
    · intro he
      subst e
      exact hvar rfl
  · rintro ⟨heb, hea, het⟩
    refine ⟨het, ⟨?_, (h.supported e het).1⟩, ?_, (h.supported e het).2⟩
    · exact fun hv => hea (hleaf e het hv)
    · intro hc
      exact (hdegree e het hc).elim hea heb

/-- Lemma 37, KKR v6, printed pp. 18–19: an earliest copy with a single incoming root
arc can be rerooted at any outgoing child. Other outgoing children are retained. -/
theorem IsFDAG.reroot_earliest (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs)
    (hai : a.incoming = true) (hbo : b.incoming = false) (hab : a.copy = b.copy)
    (he : T.Earliest a.copy)
    (hleaf : ∀ e ∈ T.arcs, e.occurrence.var = a.occurrence.var → e = a)
    (hin : ∀ e ∈ T.arcs, e.incoming = true → e.copy = a.copy → e = a) :
    (T.reroot a b).IsFDAG sem (pairFlip f a.occurrence b.occurrence) := by
  have hv := h.feasible a ha b hb hai hab
  have hba : b ≠ a := by intro hh; have := congrArg Arc.incoming hh; simp_all
  have hvars : b.occurrence.var ≠ a.occurrence.var := fun hh => hba (hleaf b hb hh)
  have hbt : a.time = b.time := congrArg Prod.snd hab
  have hbi : a.occurrence.1 = b.occurrence.1 := congrArg Prod.fst hab
  have hcopy : ∀ x ∈ T.arcs, x ≠ a → x.incoming = true → x.copy ≠ a.copy := by
    intro x hx hxa hxi hxc
    exact hxa (hin x hx hxi hxc)
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e hem
    rcases mem_reroot_arcs.mp hem with rfl | ⟨het, hea, _⟩
    · exact ⟨mem_erase.mpr ⟨hvars, (h.supported b hb).1⟩, (h.supported b hb).2⟩
    · exact ⟨mem_erase.mpr ⟨fun hh => hea (hleaf e het hh), (h.supported e het).1⟩,
        (h.supported e het).2⟩
  · intro x hx y hy hxy
    rcases mem_reroot_arcs.mp hx with rfl | ⟨hxt, _, hxb⟩ <;>
      rcases mem_reroot_arcs.mp hy with rfl | ⟨hyt, _, hyb⟩
    · rfl
    · exact (hyb (h.unique y hyt b hb hxy.symm)).elim
    · exact (hxb (h.unique x hxt b hb hxy)).elim
    · exact h.unique x hxt y hyt hxy
  · intro x hx y hy hxo hyo hxy
    rcases mem_reroot_arcs.mp hx with rfl | ⟨hxt, _, _⟩
    · simp [Arc.reverse, hbo] at hxo
    rcases mem_reroot_arcs.mp hy with rfl | ⟨hyt, _, _⟩
    · simp [Arc.reverse, hbo] at hyo
    exact h.indegree x hxt y hyt hxo hyo hxy
  · refine ⟨h.ordered.1, ?_⟩
    obtain ⟨rank, hr⟩ := h.ordered.2
    let rank' : Node F → ℕ := Sum.elim
      (fun v => if v = b.occurrence.var then 0 else rank (.inl v) + 1)
      (fun c => rank (.inr c) + 1)
    refine ⟨rank', ?_⟩
    intro x y hxy
    rcases hxy with ⟨e, hem, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
    · rcases mem_reroot_arcs.mp hem with rfl | ⟨het, _, heb⟩
      · simp [rank', Arc.source, Arc.target, Arc.reverse, hbo]
      · have heold := hr e.source e.target (Or.inl ⟨e, het, rfl, rfl⟩)
        cases hei : e.incoming
        · have hnev : e.occurrence.var ≠ b.occurrence.var := by
            intro hh
            exact heb (h.indegree e het b hb hei hbo hh)
          simpa only [Arc.source, Arc.target, hei, Bool.false_eq_true, ↓reduceIte,
            rank', Sum.elim_inl, Sum.elim_inr, ite_eq_right hnev, Nat.add_lt_add_iff_right]
            using heold
        · by_cases hev : e.occurrence.var = b.occurrence.var
          · simp [Arc.source, Arc.target, hei, rank', hev]
          · simpa only [Arc.source, Arc.target, hei, ↓reduceIte, rank', Sum.elim_inl,
              Sum.elim_inr, ite_eq_right hev, Nat.add_lt_add_iff_right] using heold
    · exact Nat.add_lt_add_right
        (hr (.inr c) (.inr d) (Or.inr ⟨c, hc, d, hd, hcd, rfl, rfl⟩)) 1
  · intro x hx y hy hxi hxy
    rcases mem_reroot_arcs.mp hx with rfl | ⟨hxt, hxa, _⟩
    · rcases mem_reroot_arcs.mp hy with rfl | ⟨hyt, _, _⟩
      · simpa only [pairFlip_self] using hv
      · change ValidLabeling sem (pairFlip (pairFlip f a.occurrence b.occurrence)
          b.occurrence y.occurrence)
        rw [pairFlip_cancel]
        exact h.feasible a ha y hyt hai (hab.trans hxy)
    · have hxc := hcopy x hxt hxa hxi
      rcases mem_reroot_arcs.mp hy with rfl | ⟨hyt, _, _⟩
      · exact (hxc (hxy.trans hab.symm)).elim
      · exact h.feasible_after_earlier hM ha hb hxt hyt hai
          (h.occurrence_ne_of_orientation_ne ha hb (by simp [hai, hbo])) hab hxi hxy
          (h.time_lt_of_earliest he hxt hxc)
  · intro x hx y hy hxi hxy htime
    rcases mem_reroot_arcs.mp hx with rfl | ⟨hxt, hxa, _⟩
    · rcases mem_reroot_arcs.mp hy with rfl | ⟨hyt, _, _⟩
      · exact (Nat.lt_irrefl b.time htime).elim
      · change ¬ ValidLabeling sem (pairFlip (pairFlip f a.occurrence b.occurrence)
          b.occurrence y.occurrence)
        rw [pairFlip_cancel]
        exact h.noShortcut a ha y hyt hai (hbi.trans hxy)
          (by simpa only [Arc.reverse, ← hbt] using htime)
    · have hxc := hcopy x hxt hxa hxi
      have htx := h.time_lt_of_earliest he hxt hxc
      rcases mem_reroot_arcs.mp hy with rfl | ⟨hyt, _, _⟩
      · change x.time < b.time at htime
        change a.time < x.time at htx
        omega
      · exact h.noShortcut_after_earlier hM ha hb hxt hyt hai
          (h.occurrence_ne_of_orientation_ne ha hb (by simp [hai, hbo])) hab hxi hxy htx htime

/-- Delete a constraint copy, retaining its variable endpoints as isolated nodes if necessary. -/
@[expose] def removeCopy (T : DAG F) (c : Copy F) : DAG F :=
  T.restrict T.vars (T.copies.erase c)

/-- The earliest-copy exchange argument also applies to two incoming ports.
This covers the terminal meeting copy in Corollary 36(1). -/
theorem IsFDAG.removeCopy (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hai : a.incoming = true)
    (hne : a.occurrence ≠ b.occurrence) (hab : a.copy = b.copy)
    (he : T.Earliest a.copy) :
    (T.removeCopy a.copy).IsFDAG sem (pairFlip f a.occurrence b.occurrence) := by
  have hs := h.restrict T.vars (T.copies.erase a.copy)
  refine ⟨h.feasible a ha b hb hai hab, hs.supported, hs.unique, hs.indegree,
    hs.ordered, ?_, ?_⟩
  · intro x hx y hy hxi hxy
    obtain ⟨hxt, _, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyt, _, _⟩ := mem_filter.mp hy
    exact h.feasible_after_earlier hM ha hb hxt hyt hai hne hab hxi hxy
      (h.time_lt_of_earliest he hxt (mem_erase.mp hxc).1)
  · intro x hx y hy hxi hxy ht
    obtain ⟨hxt, _, hxc⟩ := mem_filter.mp hx
    obtain ⟨hyt, _, _⟩ := mem_filter.mp hy
    exact h.noShortcut_after_earlier hM ha hb hxt hyt hai hne hab hxi hxy
      (h.time_lt_of_earliest he hxt (mem_erase.mp hxc).1) ht

/-- Each supported constraint copy has precisely two incident arcs, at least one incoming.
This purely graph-theoretic condition includes directed paths and two paths meeting at a copy.
It places no restriction on revisits of an original constraint at different timestamps. -/
@[expose] def PairedCopies (T : DAG F) : Prop :=
  ∀ c ∈ T.copies, ∃ a ∈ T.arcs, ∃ b ∈ T.arcs,
    a.incoming = true ∧ a.copy = c ∧ b.copy = c ∧ a ≠ b ∧
      ∀ e ∈ T.arcs, e.copy = c → e = a ∨ e = b

/-- Removing one copy preserves the two-arc condition at every remaining copy. -/
theorem PairedCopies.removeCopy (hp : T.PairedCopies) (hs : T.Supported) (c : Copy F) :
    (T.removeCopy c).PairedCopies := by
  intro d hd
  obtain ⟨hdt, hderase⟩ := mem_inter.mp hd
  have hdc := (mem_erase.mp hderase).1
  obtain ⟨a, ha, b, hb, hai, hac, hbc, hab, hpair⟩ := hp d hdt
  refine ⟨a, ?_, b, ?_, hai, hac, hbc, hab, ?_⟩
  · exact mem_filter.mpr ⟨ha, (hs a ha).1,
      mem_erase.mpr ⟨hac ▸ hdc, (hs a ha).2⟩⟩
  · exact mem_filter.mpr ⟨hb, (hs b hb).1,
      mem_erase.mpr ⟨hbc ▸ hdc, (hs b hb).2⟩⟩
  · intro e hem hed
    exact hpair e (mem_filter.mp hem).1 hed

/-- Flip every used original incidence of a DAG, independently of isolated node support. -/
@[expose] def flip (T : DAG F) (f : OccurrenceLabeling F Bool) : OccurrenceLabeling F Bool :=
  flipOn (T.arcs.image Arc.occurrence) f

private theorem image_removeCopy (h : T.IsFDAG sem f) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hab : a.copy = b.copy)
    (hp : ∀ e ∈ T.arcs, e.copy = a.copy → e = a ∨ e = b) :
    (T.removeCopy a.copy).arcs.image Arc.occurrence =
      T.arcs.image Arc.occurrence \ {a.occurrence, b.occurrence} := by
  ext o
  simp only [mem_image, mem_sdiff, mem_insert, mem_singleton, not_or]
  constructor
  · rintro ⟨e, hem, rfl⟩
    obtain ⟨het, _, hcerase⟩ := mem_filter.mp hem
    have hc := (mem_erase.mp hcerase).1
    refine ⟨⟨e, het, rfl⟩, ?_, ?_⟩
    · intro he
      exact hc (congrArg Arc.copy (h.unique e het a ha he))
    · intro he
      exact hc ((congrArg Arc.copy (h.unique e het b hb he)).trans hab.symm)
  · rintro ⟨⟨e, het, rfl⟩, hea, heb⟩
    refine ⟨e, mem_filter.mpr ⟨het, (h.supported e het).1,
      mem_erase.mpr ⟨?_, (h.supported e het).2⟩⟩, rfl⟩
    intro hc
    rcases hp e het hc with rfl | rfl
    · exact hea rfl
    · exact heb rfl

/-- Removing a two-arc constraint copy factors the full DAG flip into its first pair move
and the remaining incidence flip. Original incidences are not counted twice. -/
theorem IsFDAG.flip_removeCopy (h : T.IsFDAG sem f) {a b : Arc F}
    (ha : a ∈ T.arcs) (hb : b ∈ T.arcs) (hab : a.copy = b.copy)
    (hne : a.occurrence ≠ b.occurrence)
    (hp : ∀ e ∈ T.arcs, e.copy = a.copy → e = a ∨ e = b) :
    (T.removeCopy a.copy).flip (pairFlip f a.occurrence b.occurrence) = T.flip f := by
  rw [flip, image_removeCopy h ha hb hab hp]
  have ham : a.occurrence ∈ T.arcs.image Arc.occurrence := mem_image.mpr ⟨a, ha, rfl⟩
  have hbm : b.occurrence ∈ T.arcs.image Arc.occurrence := mem_image.mpr ⟨b, hb, rfl⟩
  funext o
  by_cases hoa : o = a.occurrence <;> by_cases hob : o = b.occurrence <;>
    by_cases hom : o ∈ T.arcs.image Arc.occurrence <;>
    simp_all [flip, pairFlip, flipOn_apply]

omit [DecidableEq V] in
/-- Corollary 36 in a stronger graph form: if every copy has two incident arcs with at least
one incoming, flipping the entire f-DAG is valid. Directed variable-to-variable paths and
two otherwise-disjoint directed paths meeting at a constraint copy are special cases.
The induction removes copies, and therefore permits repeated original constraints. -/
theorem IsFDAG.valid_flip_of_pairedCopies (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (hp : T.PairedCopies) :
    ValidLabeling sem (T.flip f) := by
  classical
  generalize hn : T.copies.card = n
  induction n using Nat.strong_induction_on generalizing T f with
  | ind n ih =>
    by_cases ht : T.copies.Nonempty
    · have hex : ∃ t, ∃ c ∈ T.copies, c.2 = t := by
        obtain ⟨c, hc⟩ := ht
        exact ⟨c.2, c, hc, rfl⟩
      obtain ⟨c, hc, hct⟩ := Nat.find_spec hex
      have he : T.Earliest c := ⟨hc, fun d hd => by
        rw [hct]
        exact Nat.find_min' hex ⟨d, hd, rfl⟩⟩
      obtain ⟨a, ha, b, hb, hai, hac, hbc, hab, hpair⟩ := hp c hc
      have hcopies : a.copy = b.copy := hac.trans hbc.symm
      have hne : a.occurrence ≠ b.occurrence := fun hh => hab (h.unique a ha b hb hh)
      have hs := h.removeCopy hM ha hb hai hne hcopies (hac ▸ he)
      have hsmall : (T.removeCopy a.copy).copies.card < n := by
        change (T.copies ∩ T.copies.erase a.copy).card < n
        rw [inter_eq_right.mpr (erase_subset _ _), ← hn]
        exact card_erase_lt_of_mem (hac ▸ hc)
      have hv := ih _ hsmall hs (hp.removeCopy h.supported a.copy) rfl
      rwa [h.flip_removeCopy ha hb hcopies hne (fun e hem hec => hpair e hem (hec.trans hac))] at hv
    · have hc : T.copies = ∅ := not_nonempty_iff_eq_empty.mp ht
      have ha : T.arcs = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ham
        have := (h.supported a ham).2
        simp only [hc, Finset.notMem_empty] at this
      simpa only [flip, ha, image_empty, flipOn_empty] using h.valid

end Surgery

/-- A feasible external step preserves the same DAG when its first port cannot exchange with
any used port. This is the direct local-exchange argument for Lemma 43: unlike the source's
proof, it needs no new minimum timestamp, and therefore also handles existing timestamp zero. -/
theorem IsFDAG.external_pair (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {a b : Occurrence F}
    (hab : a.1 = b.1) (hne : a ≠ b) (hv : ValidLabeling sem (pairFlip f a b))
    (hdis : ∀ e ∈ T.arcs, a ≠ e.occurrence ∧ b ≠ e.occurrence)
    (hcross : ∀ e ∈ T.arcs, a.1 = e.occurrence.1 →
      ¬ ValidLabeling sem (pairFlip f a e.occurrence)) :
    T.IsFDAG sem (pairFlip f a b) := by
  refine ⟨hv, h.supported, h.unique, h.indegree, h.ordered, ?_, ?_⟩
  · intro x hx y hy hxi hxy
    by_cases he : x.occurrence = y.occurrence
    · rw [he, pairFlip_self]
      exact hv
    by_cases hc : a.1 = x.occurrence.1
    · exact valid_four_occurrences hM h.valid hab hc
        (hc.trans (congrArg Prod.fst hxy)) hne (hdis x hx).1 (hdis y hy).1
        (hdis x hx).2 (hdis y hy).2 he hv (h.feasible x hx y hy hxi hxy)
        (hcross x hx hc) (hcross y hy (hc.trans (congrArg Prod.fst hxy)))
    · exact (valid_pairFlip_other_iff h.valid hab (congrArg Prod.fst hxy) (Ne.symm hc) hv).mpr
        (h.feasible x hx y hy hxi hxy)
  · intro x hx y hy hxi hxy ht
    by_cases hc : a.1 = x.occurrence.1
    · exact not_valid_four_occurrences hM h.valid hab hc (hc.trans hxy)
        hne (hdis x hx).1 (hdis y hy).1 (hdis x hx).2 (hdis y hy).2
        (h.occurrence_ne_of_time_ne hx hy (Nat.ne_of_lt ht)) hv
        (h.noShortcut x hx y hy hxi hxy ht)
        (hcross x hx hc) (hcross y hy (hc.trans hxy))
    · intro hn
      exact h.noShortcut x hx y hy hxi hxy ht
        ((valid_pairFlip_other_iff h.valid hab hxy (Ne.symm hc) hv).mp hn)

section ExternalWalk

/-- Lemma 43, KKR v6, printed p. 20, with explicit occurrence-level avoidance and
`Walk.take`/`Walk.snoc` extension conditions. Every used DAG arc is tested regardless of
orientation. Direct four-coordinate exchange replaces the source proof's temporary earlier
copy, so timestamp zero needs neither a nonexistent smaller natural nor a reindexing premise. -/
theorem IsFDAG.flip_walk_of_no_prefix_extension (h : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {w : Walk F} (hw : w.IsFWalk sem f)
    (hstart : w.start ∉ T.vars)
    (hvars : ∀ o ∈ w.edges, o.var ∉ T.vars)
    (hno : ∀ n < w.steps.length, ∀ e ∈ T.arcs, ∀ o : Occurrence F,
      o.var = (w.take n).finish → o.1 = e.occurrence.1 →
        ¬ ((w.take n).snoc o e.occurrence).IsFWalk sem f) :
    T.IsFDAG sem (w.flip f) := by
  classical
  have hprefix : ∀ n, n ≤ w.steps.length → T.IsFDAG sem ((w.take n).flip f) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa only [Walk.take, List.take_zero, Walk.flip, Walk.edges, Walk.edgesOf,
        List.flatMap_nil, List.toFinset_nil, flipOn_empty] using h
    | succ n ih =>
      intro hn
      have hlt : n < w.steps.length := by omega
      have hcurrent := ih (by omega)
      let o := w.steps[n].1
      let p := w.steps[n].2
      have hstep : w.steps[n] = (o, p) := rfl
      have hs : (w.take (n + 1)).steps = (w.take n).steps ++ [(o, p)] := by
        exact (List.take_succ_eq_append_getElem hlt).trans (by rw [hstep]; rfl)
      have hsnoc : w.take (n + 1) = (w.take n).snoc o p := by
        cases w
        exact congrArg (Walk.mk _) hs
      have hwalk := hw.1.1.take (n + 1)
      have hl := (Walk.linked_append_iff w.start (w.take n).steps [(o, p)]).mp
        (hs ▸ hwalk.1)
      have ho : o.var = (w.take n).finish := hl.2.1
      have hc : o.1 = p.1 := hl.2.2.1
      have hnd : ((w.take n).edges ++ [o, p]).Nodup := by
        have he : (w.take (n + 1)).edges = (w.take n).edges ++ [o, p] := by
          change Walk.edgesOf (w.take (n + 1)).steps = _
          rw [hs, Walk.edgesOf_append]
          rfl
        simpa only [he] using hwalk.2
      have hnd' := List.nodup_append.mp hnd
      have hop : o ≠ p := (List.nodup_cons.mp hnd'.2.1).1 ∘ List.mem_singleton.mpr
      have hnoo : o ∉ (w.take n).edges := fun hh => hnd'.2.2 o hh o (by simp) rfl
      have hnop : p ∉ (w.take n).edges := fun hh => hnd'.2.2 p hh p (by simp) rfl
      have hmem : ∀ q ∈ [o, p], q ∈ w.edges := by
        intro q hq
        exact List.mem_flatMap.mpr ⟨w.steps[n], List.getElem_mem hlt,
          by simpa only [hstep] using hq⟩
      have hom := hmem o (by simp)
      have hpm := hmem p (by simp)
      have hdis : ∀ e ∈ T.arcs, o ≠ e.occurrence ∧ p ≠ e.occurrence := by
        intro e he
        exact ⟨fun hh => hvars o hom (hh ▸ (h.supported e he).1),
          fun hh => hvars p hpm (hh ▸ (h.supported e he).1)⟩
      have hv : ValidLabeling sem (pairFlip ((w.take n).flip f) o p) := by
        rw [pairFlip_eq _ hop]
        have hv := hw.1.valid_take (n + 1) hn
        rwa [hsnoc, Walk.flip_snoc _ _ _ _ (hw.1.1.take n) hnoo hnop hop] at hv
      have hcross : ∀ e ∈ T.arcs, o.1 = e.occurrence.1 →
          ¬ ValidLabeling sem (pairFlip ((w.take n).flip f) o e.occurrence) := by
        intro e he hce hv
        have hne := (hdis e he).1
        have hnew : e.occurrence ∉ (w.take n).edges := by
          intro hm
          have hem : e.occurrence ∈ w.edges := by
            exact ((List.take_sublist n w.steps).flatMap fun (o, p) => [o, p]).subset hm
          exact hvars e.occurrence hem (h.supported e he).1
        have hi : (w.take n).steps = [] ∨ ¬ Inconsistent f (w.take n).finish := by
          by_cases hn0 : n = 0
          · subst n
            exact Or.inl rfl
          · exact Or.inr (hw.1.not_inconsistent_finish_take (by omega) hlt)
        have hsn := (hw.1.take n).snoc ho hce hne hnoo hnew hi
          (by rwa [pairFlip_eq _ hne] at hv)
        have hends : (w.take n).start ≠ ((w.take n).snoc o e.occurrence).finish := by
          rw [Walk.finish_snoc]
          exact fun hh => hstart (hh ▸ (h.supported e he).1)
        exact hno n hlt e he o ho hce ⟨hsn, hends⟩
      rw [hsnoc, Walk.flip_snoc _ _ _ _ (hw.1.1.take n) hnoo hnop hop, ← pairFlip_eq _ hop]
      exact hcurrent.external_pair hM hc hop hv hdis hcross
  have hv := hprefix w.steps.length (Nat.le_refl _)
  simpa only [Walk.take, List.take_length] using hv

end ExternalWalk

end Cslib.Logic.PL.CSP.DAG
