/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Subpath

/-!
# Internal variables of incidence trails

In an edge instance, an internal visit uses both incidences of its variable. It cannot
therefore revisit a trail's starting variable. These structural facts transfer internal
consistency through a preparatory root-path flip, using the existing exact defect equation.
-/

public section

namespace Cslib.Logic.PL.CSP.Walk

variable {Rel V : Type*} {F : CSP Rel V}

/-- Consistency at every output of the left segment permits any internally consistent
continuation. The last output is included because the continuation may be nonempty. -/
theorem InternallyConsistent.append_of_outputs {f : OccurrenceLabeling F Bool}
    {ss ts : List (Occurrence F × Occurrence F)}
    (hs : ∀ s ∈ ss, ¬ Inconsistent f s.2.var) (ht : InternallyConsistent f ts) :
    InternallyConsistent f (ss ++ ts) := by
  induction ss with
  | nil => exact ht
  | cons s ss ih =>
    exact ⟨Or.inr (hs s List.mem_cons_self),
      ih (fun t hm => hs t (List.mem_cons_of_mem s hm))⟩

/-- Internal consistency is exactly consistency at every transition between consecutive steps. -/
theorem internallyConsistent_iff_splits (f : OccurrenceLabeling F Bool)
    (ss : List (Occurrence F × Occurrence F)) :
    InternallyConsistent f ss ↔
      ∀ pre o p a b post, ss = pre ++ (o, p) :: (a, b) :: post → ¬ Inconsistent f p.var := by
  constructor
  · intro hi pre
    induction pre generalizing ss with
    | nil =>
      intro o p a b post he
      subst ss
      exact hi.1.resolve_left (by simp)
    | cons s pre ih =>
      intro o p a b post he
      subst ss
      exact ih _ hi.2 o p a b post rfl
  · intro hi
    induction ss with
    | nil => trivial
    | cons s ss ih =>
      refine ⟨?_, ih (fun pre o p a b post he => hi (s :: pre) o p a b post
        (by simp only [List.cons_append, he]))⟩
      cases ss with
      | nil => exact Or.inl rfl
      | cons t ss => exact Or.inr (hi [] s.1 s.2 t.1 t.2 ss rfl)

/-- An internal variable cannot equal the starting variable of an incidence trail in an
edge instance: the transition would need a third distinct incidence at that variable. -/
theorem IsWalk.internal_var_ne_start (hF : EdgeInstance F) {w : Walk F} (hw : w.IsWalk)
    {pre post : List (Occurrence F × Occurrence F)} {o p a b : Occurrence F}
    (he : w.steps = pre ++ (o, p) :: (a, b) :: post) : p.var ≠ w.start := by
  have hl := hw.1
  rw [he, linked_append_iff] at hl
  have hap : a.var = p.var := hl.2.2.2.1
  have hn := hw.2
  change (edgesOf w.steps).Nodup at hn
  rw [he, edgesOf_append] at hn
  have hports := (List.nodup_append.mp hn).2.1
  change (o :: p :: a :: b :: edgesOf post).Nodup at hports
  have hpa : p ≠ a := by
    intro he
    subst a
    exact (List.nodup_cons.mp (List.nodup_cons.mp hports).2).1 List.mem_cons_self
  intro hp
  cases pre with
  | nil =>
    have hv : o.var = p.var := hl.2.1.trans hp.symm
    have heq := hF.eq_of_constraint_eq hv hl.2.2.1
    cases heq
    exact (List.nodup_cons.mp hports).1 List.mem_cons_self
  | cons s pre =>
    rcases s with ⟨r, q⟩
    have hroot : r.var = w.start := hl.1.1
    change (r :: q :: (edgesOf pre ++ o :: p :: a :: b :: edgesOf post)).Nodup at hn
    have hrnot := (List.nodup_cons.mp hn).1
    have hrp : r ≠ p := fun he => hrnot (he.symm ▸ (by simp))
    have hra : r ≠ a := fun he => hrnot (he.symm ▸ (by simp))
    rcases hF.eq_or_eq_partner (hroot.trans hp.symm) with he | he
    · exact hrp he
    · rcases hF.eq_or_eq_partner hap with ha | ha
      · exact hpa ha.symm
      · exact hra (he.trans ha.symm)

open scoped symmDiff in
/-- Preparing a walk's base by a trail from an inconsistent root preserves all of the
walk's original internal consistency. Validity of labelings is a separate obligation. -/
theorem IsWalk.internallyConsistent_flip (hF : EdgeInstance F)
    {w prep : Walk F} (hw : w.IsWalk) (hp : prep.IsWalk) (f : OccurrenceLabeling F Bool)
    (he : prep.finish = w.start) (hr : Inconsistent f prep.start)
    (hi : InternallyConsistent f w.steps) : InternallyConsistent (prep.flip f) w.steps := by
  classical
  apply (internallyConsistent_iff_splits _ _).mpr
  intro pre o p a b post hs
  have hcons := (internallyConsistent_iff_splits f w.steps).mp hi pre o p a b post hs
  have hbase := hw.internal_var_ne_start hF hs
  have hroot : p.var ≠ prep.start := fun he => hcons (he.symm ▸ hr)
  have hfinish : p.var ≠ prep.finish := by rwa [he]
  rw [← mem_defects, hp.defects_flip hF]
  simp [Finset.mem_symmDiff, Finset.mem_singleton, hroot, hfinish, mem_defects, hcons]

end Cslib.Logic.PL.CSP.Walk
