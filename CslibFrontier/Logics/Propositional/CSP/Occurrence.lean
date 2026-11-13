/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Vars
import CslibFrontier.Logics.Propositional.CNF.Occurrence
import Mathlib.Data.List.OfFn

/-!
# Ordered argument occurrences of CSP instances

An occurrence is a constraint position together with a position in its scope. Neither repeated
constraints nor repeated variables are identified. Local labelings read scopes in argument order;
consistency requires equal labels at all occurrences of a variable. A consistent local labeling
reconstructs a global assignment, using an explicitly supplied value for nonoccurring variables.
These definitions use the existing `CSP` and its arbitrary-domain semantics.

## Main definitions

* `Cslib.Logic.PL.CSP.Occurrence`: dependent indices into the existing instance.
* `Cslib.Logic.PL.CSP.occurrences`: executable records in constraint-then-scope order.
* `Cslib.Logic.PL.CSP.ValidLabeling`, `Cslib.Logic.PL.CSP.ConsistentLabeling`: local validity
  and agreement on variables.
* `Cslib.Logic.PL.CSP.EdgeInstance`: every occurring variable has precisely two occurrences,
  in distinct constraint positions.

## References

The Boolean specialization of `EdgeInstance` matches [KazdaKolmogorovRolinek2018], Section 2,
Definition 3 (arXiv v6, p. 3). That source uses set scopes; the distinct-position and exactly-two
requirements here explicitly enforce its no-repeat convention without normalizing input scopes.
Local validity and agreement specialize Section 5.1, Definition 20. The occurrence enumeration
and reconstruction proofs are original, and impose no planarity or arity bound.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V D : Type*} {F : CSP Rel V}

/-- A constraint position and an argument position in that constraint's ordered scope. -/
abbrev Occurrence (F : CSP Rel V) := (i : Fin F.length) × Fin F[i.val].scope.length

namespace Occurrence

/-- Relation symbol at this occurrence's constraint position. -/
@[expose] def relation (o : Occurrence F) : Rel := F[o.1.val].rel

/-- Ordered scope at this occurrence's constraint position. -/
@[expose] def scope (o : Occurrence F) : List V := F[o.1.val].scope

/-- Variable at this argument position, retaining repeated occurrences. -/
@[expose] def var (o : Occurrence F) : V := F[o.1.val].scope[o.2.val]

/-- Executable record: constraint index, scope index, variable. -/
@[expose] def record (o : Occurrence F) : ℕ × ℕ × V := (o.1, o.2, o.var)

/-- The two position indices identify an occurrence independently of variable names. -/
theorem record_injective : Function.Injective (record (F := F)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hi : i = i' := Fin.ext (congrArg (fun r => r.1) h)
  subst i'
  have hj : j = j' := Fin.ext (congrArg (fun r => r.2.1) h)
  subst j'
  rfl

/-- Every named variable is an occurring variable of the original CSP. -/
theorem var_mem (o : Occurrence F) : o.var ∈ F.vars :=
  List.mem_flatMap.mpr ⟨F[o.1.val], List.getElem_mem _, List.getElem_mem _⟩

end Occurrence

/-- Every occurring variable has a constraint-position/scope-position witness. -/
theorem exists_occurrence_iff (v : V) :
    (∃ o : Occurrence F, o.var = v) ↔ v ∈ F.vars := by
  constructor
  · rintro ⟨o, rfl⟩
    exact o.var_mem
  · intro hv
    obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    obtain ⟨j, hj, h⟩ := List.mem_iff_getElem.mp hv
    exact ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, h⟩

/-- Occurrence records in constraint order, then scope order. The positive-CNF adapter preserves
all positions and lets us reuse the existing executable occurrence enumeration. -/
@[expose] def occurrences (F : CSP Rel V) : List (ℕ × ℕ × V) :=
  (Cslib.Logic.PL.occurrences F.varCNF).map fun o => (o.clause, o.pos, o.lit.1)

/-- The enumeration contains exactly the valid position/variable records. -/
theorem mem_occurrences {r : ℕ × ℕ × V} :
    r ∈ F.occurrences ↔ ∃ o : Occurrence F, o.record = r := by
  rcases r with ⟨i, j, v⟩
  simp only [occurrences, List.mem_map, Cslib.Logic.PL.mem_occurrences]
  constructor
  · rintro ⟨⟨i', j', v', b⟩, ⟨hi, hj, he⟩, hr⟩
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    simp only [varCNF, List.length_map, List.getElem_map] at hi hj he
    exact ⟨⟨⟨i', hi⟩, ⟨j', hj⟩⟩, by
      simp only [Occurrence.record, Occurrence.var, Prod.mk.injEq, true_and]
      exact congrArg Prod.fst he.symm⟩
  · rintro ⟨⟨⟨i', hi⟩, ⟨j', hj⟩⟩, hr⟩
    cases hr
    refine ⟨⟨i', j', (F[i'].scope[j'], true)⟩, ?_, rfl⟩
    exact ⟨by simpa only [varCNF, List.length_map] using hi,
      by simpa only [varCNF, List.getElem_map, List.length_map] using hj, by
        simp only [varCNF, List.getElem_map]⟩

/-- Forgetting positions gives the original occurrence list, including repetitions. -/
theorem map_occurrences (F : CSP Rel V) : F.occurrences.map (fun o => o.2.2) = F.vars := by
  simpa only [occurrences, List.map_map, Function.comp_def, vars_varCNF] using
    Cslib.Logic.PL.map_occurrences F.varCNF

/-- Every position record occurs exactly once, even if its variable or constraint is repeated. -/
theorem occurrences_nodup (F : CSP Rel V) : F.occurrences.Nodup := by
  have polarity (o : Cslib.Logic.PL.Occurrence V)
      (ho : o ∈ Cslib.Logic.PL.occurrences F.varCNF) : o.lit.2 = true := by
    obtain ⟨hi, hj, he⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
    simpa only [varCNF, List.getElem_map] using congrArg Prod.snd he
  apply (Cslib.Logic.PL.occurrences_nodup F.varCNF).map_on
  intro a ha b hb hab
  simp only [Prod.mk.injEq] at hab
  exact Cslib.Logic.PL.Occurrence.ext hab.1 hab.2.1
    (Prod.ext hab.2.2 ((polarity a ha).trans (polarity b hb).symm))

/-- The number of argument occurrences is the sum of the scope lengths. -/
theorem length_occurrences (F : CSP Rel V) :
    F.occurrences.length = (F.map fun c => c.scope.length).sum := by
  rw [← List.length_map (f := fun o : ℕ × ℕ × V => o.2.2), map_occurrences]
  simp [vars, List.length_flatMap]

/-- A local labeling assigns a domain value separately to each argument occurrence. -/
abbrev OccurrenceLabeling (F : CSP Rel V) (D : Type*) := Occurrence F → D

/-- The tuple at a constraint reads its argument labels in their original order. -/
@[expose] def localTuple (l : OccurrenceLabeling F D) (i : Fin F.length) : List D :=
  List.ofFn fun j => l ⟨i, j⟩

/-- Every constraint accepts its own ordered tuple of occurrence labels. -/
@[expose] def ValidLabeling (sem : Rel → List D → Bool) (l : OccurrenceLabeling F D) : Prop :=
  ∀ i : Fin F.length, sem F[i].rel (localTuple l i) = true

/-- All occurrences of the same variable have the same label. -/
@[expose] def ConsistentLabeling (l : OccurrenceLabeling F D) : Prop :=
  ∀ o p : Occurrence F, o.var = p.var → l o = l p

/-- Restrict a global assignment to the ordered argument occurrences. -/
@[expose] def labelAssignment (σ : V → D) : OccurrenceLabeling F D := fun o => σ o.var

/-- Global assignments always induce consistent labels. -/
theorem consistentLabeling_labelAssignment (σ : V → D) :
    ConsistentLabeling (labelAssignment (F := F) σ) := fun _ _ h => congrArg σ h

/-- Restricting an assignment preserves each constraint's ordered tuple. -/
@[simp] theorem localTuple_labelAssignment (σ : V → D) (i : Fin F.length) :
    localTuple (labelAssignment σ) i = F[i].scope.map σ := by
  exact List.ofFn_getElem_eq_map _ _

/-- Local validity of assignment labels is exactly the existing CSP evaluation. -/
theorem validLabeling_labelAssignment_iff (sem : Rel → List D → Bool) (σ : V → D) :
    ValidLabeling sem (labelAssignment (F := F) σ) ↔ F.eval sem σ = true := by
  simp only [ValidLabeling, localTuple_labelAssignment, eval, List.all_eq_true,
    Constraint.eval]
  constructor
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact h ⟨i, hi⟩
  · intro h i
    exact h _ (List.getElem_mem _)

/-- Recover an assignment by choosing one occurrence of each occurring variable; `outside` is
the value on every variable absent from the instance. -/
noncomputable def reconstruct (l : OccurrenceLabeling F D) (outside : D) : V → D :=
  open Classical in
  fun v => if h : ∃ o : Occurrence F, o.var = v then l h.choose else outside

/-- The reconstructed assignment has precisely the supplied value off the occurring variables. -/
theorem reconstruct_of_not_mem (l : OccurrenceLabeling F D) (outside : D) {v : V}
    (hv : v ∉ F.vars) : reconstruct l outside v = outside := by
  have h : ¬ ∃ o : Occurrence F, o.var = v := by
    rwa [exists_occurrence_iff]
  simp [reconstruct, h]

/-- Consistency makes reconstruction independent of the chosen representative occurrence. -/
theorem reconstruct_variable {l : OccurrenceLabeling F D} (h : ConsistentLabeling l)
    (outside : D) (o : Occurrence F) : reconstruct l outside o.var = l o := by
  have ho : ∃ p : Occurrence F, p.var = o.var := ⟨o, rfl⟩
  simp only [reconstruct, dite_eq_left ho]
  exact h _ _ ho.choose_spec

/-- A consistent valid local labeling reconstructs a model of the original CSP. -/
theorem eval_reconstruct {sem : Rel → List D → Bool} {l : OccurrenceLabeling F D}
    (hl : ValidLabeling sem l) (hc : ConsistentLabeling l) (outside : D) :
    F.eval sem (reconstruct l outside) = true := by
  apply (validLabeling_labelAssignment_iff sem _).mp
  have h : labelAssignment (reconstruct l outside) = l :=
    funext (reconstruct_variable hc outside)
  rwa [h]

/-- Consistent occurrence labels are exactly restrictions of global assignments. -/
theorem consistentLabeling_iff_exists_assignment (l : OccurrenceLabeling F D) (outside : D) :
    ConsistentLabeling l ↔ ∃ σ : V → D, labelAssignment σ = l := by
  constructor
  · intro h
    exact ⟨reconstruct l outside, funext (reconstruct_variable h outside)⟩
  · rintro ⟨σ, rfl⟩
    exact consistentLabeling_labelAssignment σ

/-- Satisfiability is equivalent to existence of a valid, consistent occurrence labeling. -/
theorem satisfiable_iff_exists_labeling (sem : Rel → List D → Bool) (outside : D) :
    F.Satisfiable sem ↔ ∃ l : OccurrenceLabeling F D,
      ValidLabeling sem l ∧ ConsistentLabeling l := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨labelAssignment σ, (validLabeling_labelAssignment_iff sem σ).mpr hσ,
      consistentLabeling_labelAssignment σ⟩
  · rintro ⟨l, hl, hc⟩
    exact ⟨reconstruct l outside, eval_reconstruct hl hc outside⟩

/-- Every occurring variable appears exactly twice, at distinct constraint positions. This also
excludes repetitions within one scope, without changing the instance. -/
@[expose] def EdgeInstance (F : CSP Rel V) : Prop :=
  ∀ o : Occurrence F, ∃ p : Occurrence F, o.1 ≠ p.1 ∧ o.var = p.var ∧
    ∀ q : Occurrence F, q.var = o.var → q = o ∨ q = p

namespace EdgeInstance

variable (h : EdgeInstance F)

/-- The other occurrence of an edge variable. -/
noncomputable def partner (o : Occurrence F) : Occurrence F := (h o).choose

/-- An edge's two occurrences belong to different constraint positions. -/
theorem partner_constraint_ne (o : Occurrence F) : o.1 ≠ (h.partner o).1 :=
  (h o).choose_spec.1

/-- Both ends of an edge name the same variable. -/
theorem partner_variable (o : Occurrence F) : o.var = (h.partner o).var :=
  (h o).choose_spec.2.1

/-- The partner is a genuinely different argument occurrence. -/
theorem partner_ne (o : Occurrence F) : o ≠ h.partner o :=
  fun he => h.partner_constraint_ne o (congrArg Sigma.fst he)

/-- A variable has no occurrences beyond these two ends. -/
theorem eq_or_eq_partner {o p : Occurrence F} (hp : p.var = o.var) :
    p = o ∨ p = h.partner o := (h o).choose_spec.2.2 p hp

include h in
/-- Each of the two constraint scopes contains the variable only once. -/
theorem eq_of_constraint_eq {o p : Occurrence F} (hv : o.var = p.var) (hi : o.1 = p.1) :
    o = p := by
  rcases h.eq_or_eq_partner hv.symm with hp | hp
  · exact hp.symm
  · exact (h.partner_constraint_ne o (hi.trans (congrArg Sigma.fst hp))).elim

/-- Taking the other end twice returns the original argument occurrence. -/
@[simp] theorem partner_partner (o : Occurrence F) : h.partner (h.partner o) = o := by
  rcases h.eq_or_eq_partner ((h.partner_variable (h.partner o)).symm.trans
      (h.partner_variable o).symm) with hp | hp
  · exact hp
  · exact (h.partner_ne (h.partner o) hp.symm).elim

/-- The two endpoint labels agree on each edge variable. -/
@[expose] def Agrees (l : OccurrenceLabeling F D) : Prop := ∀ o, l o = l (h.partner o)

/-- For edge instances, agreement of the two endpoint labels is exactly global consistency. -/
theorem agrees_iff_consistent (l : OccurrenceLabeling F D) :
    h.Agrees l ↔ ConsistentLabeling l := by
  constructor
  · intro hl o p hp
    rcases h.eq_or_eq_partner hp.symm with rfl | rfl
    · rfl
    · exact hl o
  · intro hl o
    exact hl _ _ (h.partner_variable o)

/-- A model exists iff there is a valid local labeling with agreeing endpoints on every edge.
This includes the empty instance and retains nullary constraints. -/
theorem satisfiable_iff_exists_agrees (sem : Rel → List D → Bool) (outside : D) :
    F.Satisfiable sem ↔ ∃ l : OccurrenceLabeling F D, ValidLabeling sem l ∧ h.Agrees l := by
  simp only [satisfiable_iff_exists_labeling sem outside, h.agrees_iff_consistent]

end EdgeInstance

end Cslib.Logic.PL.CSP
