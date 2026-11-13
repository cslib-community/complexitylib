/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Positions
public import CslibFrontier.Foundations.Data.List.FlatMapPositions

/-!
# Literal occurrence positions in concatenated CSP bodies

Each occurrence in a selected body keeps its argument position and shifts its constraint
position by the actual preceding body lengths. Empty bodies and duplicate constraints are
retained. This is positional list mathematics, with no equality assumption on variable names.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {α : Type*} {Rel V : Type}

/-- Place one body's occurrence at its literal position in a flat-mapped CSP. -/
@[expose] def flatMapOccurrence (l : List α) (f : α → CSP Rel V) (i : Fin l.length)
    (o : (f l[i.val]).Occurrence) : Occurrence (l.flatMap f) :=
  ⟨⟨((l.take i.val).flatMap f).length + o.1.val,
      List.flatMap_prefix_add_lt l f i.isLt o.1.isLt⟩,
    ⟨o.2.val, by
      rw [List.getElem_flatMap_prefix_add l f i.isLt o.1.isLt]
      exact o.2.isLt⟩⟩

/-- The copied occurrence's actual constraint position includes precisely the preceding
listed bodies, with no deduplication or offset determined by a variable name. -/
theorem flatMapOccurrence_constraint (l : List α) (f : α → CSP Rel V) (i : Fin l.length)
    (o : (f l[i.val]).Occurrence) :
    (flatMapOccurrence l f i o).1.val = ((l.take i.val).flatMap f).length + o.1.val := rfl

/-- The original ordered argument position is unchanged by concatenating bodies. -/
theorem flatMapOccurrence_argument (l : List α) (f : α → CSP Rel V) (i : Fin l.length)
    (o : (f l[i.val]).Occurrence) : (flatMapOccurrence l f i o).2.val = o.2.val := rfl

/-- The target getter reads the original variable at the actual local occurrence. -/
theorem var_flatMapOccurrence (l : List α) (f : α → CSP Rel V) (i : Fin l.length)
    (o : (f l[i.val]).Occurrence) : (flatMapOccurrence l f i o).var = o.var := by
  unfold Occurrence.var flatMapOccurrence
  simp only [List.getElem_flatMap_prefix_add l f i.isLt o.1.isLt]

/-- Distinct copy/local positions remain distinct occurrences, even when constraints and
all their variable names coincide. -/
theorem flatMapOccurrence_injective (l : List α) (f : α → CSP Rel V) :
    Function.Injective (fun p : (i : Fin l.length) × (f l[i.val]).Occurrence =>
      flatMapOccurrence l f p.1 p.2) := by
  rintro ⟨i, o⟩ ⟨j, p⟩ he
  have hpos := List.flatMap_prefix_add_injective l f i.isLt o.1.isLt j.isLt p.1.isLt
    (congrArg (fun q => q.1.val) he)
  have hij : i = j := Fin.ext hpos.1
  subst j
  have hop : o = p := Occurrence.eq_of_positions hpos.2 (congrArg (fun q => q.2.val) he)
  subst p
  rfl

/-- Every flat occurrence belongs to one actual source body, including in the presence
of arbitrary empty bodies between the selected positions. -/
theorem exists_flatMapOccurrence (l : List α) (f : α → CSP Rel V)
    (o : Occurrence (l.flatMap f)) :
    ∃ (i : Fin l.length) (p : (f l[i.val]).Occurrence), flatMapOccurrence l f i p = o := by
  obtain ⟨i, hi, j, hj, he⟩ := List.exists_flatMap_prefix_add l f o.1.isLt
  have hrow : (l.flatMap f)[o.1.val]'o.1.isLt = (f l[i])[j] := by
    simpa only [← he] using List.getElem_flatMap_prefix_add l f hi hj
  let p : (f l[i]).Occurrence := ⟨⟨j, hj⟩, ⟨o.2.val, by rw [← hrow]; exact o.2.isLt⟩⟩
  exact ⟨⟨i, hi⟩, p, Occurrence.eq_of_positions he.symm rfl⟩

end Cslib.Logic.PL.CSP
