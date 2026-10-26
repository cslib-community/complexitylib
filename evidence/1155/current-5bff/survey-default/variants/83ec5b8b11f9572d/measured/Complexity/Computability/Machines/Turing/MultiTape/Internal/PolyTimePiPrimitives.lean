/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
import Complexity.Foundations.Data.List.Fold
import Mathlib.Data.List.GetD


import Diag1155.Measure
/-!
# Direct finite-table construction, lookup and update

The fixed index order and framed-list representation are unchanged. Lookup composes the existing
head and tail codec machines; finite runtime dispatch retains the full captured input in each
branch. The direct proofs introduce no default inhabitant requirement on the value or index type.
-/


diag1155_install
@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases {α β Tag : Type} [Finite Tag]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {tagEncoding : Tag ↪ List Bool}
    {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableInPolyTime (branch choice) input output) :
    ComputableInPolyTime (fun a => branch (tag a) a) input output := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInPolyTime (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        have htest := (of_finite (encIn := tagEncoding) (encOut := encBool)
          fun t : Tag => decide (t = choice)).comp htag
        simpa only [List.foldr_cons, Function.comp_def, Bool.decide_iff] using
          (htest.ite (hbranch choice) ih)
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

/-- Construct a list of a fixed number of efficiently computed entries. -/
@[fun_prop]
theorem ofFn {count : ℕ} {values : α → Fin count → Value}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input enc) :
    ComputableInPolyTime (fun a => List.ofFn (values a)) input (encList enc) := by
  induction count with
  | zero => simpa using (const (encIn := input) (encOut := encList enc) [])
  | succ count ih =>
    simpa only [List.ofFn_succ] using (hvalues 0).cons'
      (ih (values := fun a i => values a i.succ) (fun i => hvalues i.succ))

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
@[fun_prop]
theorem pi [Fintype Index] {values : α → Index → Value}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input enc) :
    ComputableInPolyTime values input (encPi enc) :=
  (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq (fun _ => rfl)

private theorem listTail :
    ComputableInPolyTime (List.tail : List Value → List Value) (encList enc) (encList enc) := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.tail (enc₁ := enc) (enc := encList enc)
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    k, Q, hfin, tm, fun l => htm l⟩

private theorem listHeadD (fallback : Value) :
    ComputableInPolyTime (fun l : List Value => l.headD fallback) (encList enc) enc := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.headD
    (enc₁ := enc) (enc := encList enc) fallback
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    k, Q, hfin, tm, fun l => htm l⟩

private theorem fixedDrop (count : ℕ) :
    ComputableInPolyTime (fun l : List Value => l.drop count) (encList enc) (encList enc) := by
  induction count with
  | zero => simpa only [List.drop_zero] using (id' (encIn := encList enc))
  | succ count ih =>
    simpa only [Function.comp_def, List.tail_drop] using listTail.comp ih

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableInPolyTime (fun values : Index → Value => values i) (encPi enc) enc := by
  classical
  cases isEmpty_or_nonempty Value with
  | inl hempty =>
    let : IsEmpty (Index → Value) := ⟨fun values => isEmptyElim (values i)⟩
    exact of_finite _
  | inr hnonempty =>
    have hlist : ComputableInPolyTime (fun values : Index → Value =>
        List.ofFn (fun j => values ((Fintype.equivFin Index).symm j)))
        (encPi enc) (encList enc) := of_eq (fun _ => rfl)
    have hlookup := (listHeadD (enc := enc) (Classical.choice hnonempty)).comp
      ((fixedDrop (enc := enc) (Fintype.equivFin Index i).val).comp hlist)
    simpa [Function.comp_def, List.headD_eq_getD, List.getD_eq_getElem?_getD] using hlookup

/-- Update a fixed table entry while charging for all preserved entries. -/
@[fun_prop]
theorem pi_update [Fintype Index] [DecidableEq Index]
    {values : α → Index → Value} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hvalue : ComputableInPolyTime value input enc) (i : Index) :
    ComputableInPolyTime (fun a => Function.update (values a) i (value a))
      input (encPi enc) := by
  apply pi
  intro j
  by_cases h : j = i
  · subst j
    simpa using hvalue
  · simpa [Function.update_of_ne h, Function.comp_def] using (pi_apply enc j).comp hvalues

/-- Read a computed index of a fixed finite table, charging the index and all stored entries. -/
theorem pi_apply' [Fintype Index] {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) input enc :=
  hindex.finite_cases (fun i => (pi_apply enc i).comp hvalues)

/-- Update a computed index while retaining and charging every other entry. -/
@[fun_prop]
theorem pi_update' [Fintype Index] [DecidableEq Index] {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding)
    (hvalue : ComputableInPolyTime value input enc) :
    ComputableInPolyTime (fun a => Function.update (values a) (index a) (value a))
      input (encPi enc) := hindex.finite_cases (fun i => pi_update hvalues hvalue i)

end Turing.MultiTapeTM.ComputableInPolyTime
