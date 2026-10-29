/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Polynomial-time finite table operations

Programs construct finite tables as ordinary functions and use ordinary application and update.
The certificates store the complete table using `encPi` and the existing list machinery.
The index type is fixed independently of the input; values need not be finite or inhabited.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.ofFn`, `.pi`: construct fixed finite families.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply`, `.pi_update`: fixed-index access.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply'`: computed-index access.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_eval`: lookup from an encoded table/index pair.

## References

Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy deterministic calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- Construct a list of a fixed number of efficiently computed entries. -/
@[fun_prop]
theorem ofFn {count : ℕ} {values : α → Fin count → Value}
    (hvalues : ∀ i, ComputableTidilyInPolyTime (fun a => values a i) input enc) :
    ComputableTidilyInPolyTime (fun a => List.ofFn (values a)) input (encList enc) := by
  induction count with
  | zero => simpa using (const (encIn := input) (encMid := encList enc) [])
  | succ count ih =>
    simpa only [List.ofFn_succ] using (hvalues 0).cons'
      (ih (values := fun a i => values a i.succ) (fun i => hvalues i.succ))

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
@[fun_prop]
theorem pi [Fintype Index] {values : α → Index → Value}
    (hvalues : ∀ i, ComputableTidilyInPolyTime (fun a => values a i) input enc) :
    ComputableTidilyInPolyTime values input (encPi enc) :=
  (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq (fun _ => rfl)

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableTidilyInPolyTime (fun values : Index → Value => values i) (encPi enc) enc := by
  classical
  cases isEmpty_or_nonempty Value with
  | inl hempty =>
    let : IsEmpty (Index → Value) := ⟨fun values => isEmptyElim (values i)⟩
    exact of_finite _
  | inr hnonempty =>
    have hlist : ComputableTidilyInPolyTime (fun values : Index → Value =>
        List.ofFn (fun j => values ((Fintype.equivFin Index).symm j)))
        (encPi enc) (encList enc) := of_eq (fun _ => rfl)
    have hlookup := (listGetD (encA := enc) (Classical.choice hnonempty)).comp
      (hlist.prod (const (encMid := encUnary) (Fintype.equivFin Index i).val))
    simpa [Function.comp_def] using hlookup

/-- Update a fixed table entry while charging for all preserved entries. -/
@[fun_prop]
theorem pi_update [Fintype Index] [DecidableEq Index]
    {values : α → Index → Value} {value : α → Value}
    (hvalues : ComputableTidilyInPolyTime values input (encPi enc))
    (hvalue : ComputableTidilyInPolyTime value input enc) (i : Index) :
    ComputableTidilyInPolyTime (fun a => Function.update (values a) i (value a))
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
    (hvalues : ComputableTidilyInPolyTime values input (encPi enc))
    (hindex : ComputableTidilyInPolyTime index input indexEncoding) :
    ComputableTidilyInPolyTime (fun a => values a (index a)) input enc :=
  hindex.finite_cases (fun i => (pi_apply enc i).comp hvalues)

/-- Evaluate a stored table at a stored index. The product view is registered with `fun_prop`;
for separately computed tables and indices, apply `pi_apply'` to their certificates. -/
@[fun_prop]
theorem pi_eval [Fintype Index] (indexEncoding : Index ↪ List Bool) (enc : Value ↪ List Bool) :
    ComputableTidilyInPolyTime (fun pair : (Index → Value) × Index => pair.1 pair.2)
      (encPair (encPi enc) indexEncoding) enc := pi_apply' (fst _ _) (snd _ _)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
