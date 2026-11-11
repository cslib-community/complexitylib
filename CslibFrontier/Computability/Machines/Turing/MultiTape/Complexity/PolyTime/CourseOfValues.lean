/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.CourseOfValues
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-!
# Polynomial-time course-of-values tables

Polynomial-time certificates for `List.courseOfValues step n`, where stage `i` reads the table of
earlier values `[val 0, …, val (i - 1)]` and appends `step` of that prefix. Framed lists
(`encList encElem`) need only a polynomial bound on `(encElem (val i)).length` along
reachable prefixes `i < n`; raw Boolean stage tables (`encBits`) need no separate bound because
each stage appends one bit.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.courseOfValuesWith_of_tableBound`: general table-bound
  certificate for any list encoding supporting element append.
* `Turing.MultiTapeTM.ComputableInPolyTime.courseOfValuesWith`: framed-list certificate with a
  captured parameter and unary count.
* `Turing.MultiTapeTM.ComputableInPolyTime.courseOfValuesWithInput`: captured-input specialization.
* `Turing.MultiTapeTM.ComputableInPolyTime.courseOfValues`: unary-input framed-list certificate.
* `Turing.MultiTapeTM.ComputableInPolyTime.courseOfValuesVal`: unary-input value certificate.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsCourseOfValuesWith`: captured Boolean-table
  certificate on `encBits`, without an explicit element bound.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsCourseOfValues`: unary-input Boolean-table
  certificate on `encBits`, without an explicit element bound.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsCourseOfValuesVal`: unary-input Boolean value
  certificate on `encBits`, without an explicit element bound.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

private theorem bitsSnoc :
    ComputableInPolyTime (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair encBits encBool) encBits := by
  fun_prop

/-- **Course-of-values certificate for any list encoding supporting single-element append.**
A captured parameter `par`, unary stage count `count`, and polynomial bound on the encoded
reachable prefix tables `List.courseOfValues (step (par x)) i` (`i ≤ count x`) suffice. -/
theorem courseOfValuesWith_of_tableBound {γ π β : Type}
    {encIn : γ ↪ List Bool} {encPar : π ↪ List Bool}
    {encElem : β ↪ List Bool} {encL : List β ↪ List Bool}
    {par : γ → π} {count : γ → ℕ} {step : π → List β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : π × List β => step p.1 p.2)
      (encPair encPar encL) encElem)
    (hsnoc : ComputableInPolyTime (fun p : List β × β => p.1 ++ [p.2])
      (encPair encL encElem) encL)
    {bound : γ → ℕ}
    (hbound : PolyBounded (fun x => (encIn x).length) bound)
    (htables : ∀ x, ∀ i ≤ count x,
      (encL (List.courseOfValues (step (par x)) i)).length ≤ bound x) :
    ComputableInPolyTime (fun x => List.courseOfValues (step (par x)) (count x)) encIn encL := by
  have hiter :=
    iterateWith (par := par) (count := count) (init := fun _ : γ => ([] : List β))
    (step := fun p T => T ++ [step p T])
    hpar hcount (const [])
    (hsnoc.comp ((snd encPar encL).prod hstep))
    hbound fun x i hi => by
      simpa only [← List.courseOfValues_eq_iterate] using htables x i hi
  simpa only [← List.courseOfValues_eq_iterate] using hiter

/-- **Course-of-values certificate for framed lists** with a captured parameter `par` and unary
stage count `count`. Only the values produced along reachable prefixes `i < count x` need a
polynomial size bound. -/
theorem courseOfValuesWith {γ π β : Type}
    {encIn : γ ↪ List Bool} {encPar : π ↪ List Bool} {encElem : β ↪ List Bool}
    {par : γ → π} {count : γ → ℕ} {step : π → List β → β}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : π × List β => step p.1 p.2)
      (encPair encPar (encList encElem)) encElem)
    {elemBound : γ → ℕ}
    (hbound : PolyBounded (fun x => (encIn x).length) elemBound)
    (helem : ∀ x, ∀ i < count x,
      (encElem (List.courseOfValuesVal (step (par x)) i)).length ≤ elemBound x) :
    ComputableInPolyTime (fun x => List.courseOfValues (step (par x)) (count x))
      encIn (encList encElem) := by
  refine courseOfValuesWith_of_tableBound hpar hcount hstep (snoc encElem)
    (hcount.polyBounded.mul (((PolyBounded.const 2).mul hbound).add (.const 1)))
    fun x i hi => ?_
  calc (encList encElem (List.courseOfValues (step (par x)) i)).length
      ≤ (List.courseOfValues (step (par x)) i).length * (2 * elemBound x + 1) :=
        length_encList_le encElem _ fun a ha => by
          obtain ⟨m, hm, rfl⟩ := List.mem_courseOfValues.mp ha
          exact helem x m (Nat.lt_of_lt_of_le hm hi)
    _ ≤ count x * (2 * elemBound x + 1) := by
        rw [List.length_courseOfValues]
        exact Nat.mul_le_mul_right _ hi

/-- Course-of-values recursion on framed lists capturing the original input directly. -/
theorem courseOfValuesWithInput {γ β : Type}
    {encIn : γ ↪ List Bool} {encElem : β ↪ List Bool}
    {count : γ → ℕ} {step : γ → List β → β}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List β => step p.1 p.2)
      (encPair encIn (encList encElem)) encElem)
    {elemBound : γ → ℕ}
    (hbound : PolyBounded (fun x => (encIn x).length) elemBound)
    (helem : ∀ x, ∀ i < count x,
      (encElem (List.courseOfValuesVal (step x) i)).length ≤ elemBound x) :
    ComputableInPolyTime (fun x => List.courseOfValues (step x) (count x))
      encIn (encList encElem) :=
  courseOfValuesWith id' hcount hstep hbound helem

/-- **Course-of-values recursion from unary stage `n`** on framed lists. Bounding the encoded
entry `List.courseOfValuesVal step i` for every `i < n` by a polynomially bounded function of `n`
certifies `List.courseOfValues step`. -/
theorem courseOfValues {β : Type} {encElem : β ↪ List Bool} {step : List β → β}
    (hstep : ComputableInPolyTime step (encList encElem) encElem)
    {elemBound : ℕ → ℕ} (hbound : PolynomiallyBounded elemBound)
    (helem : ∀ n, ∀ i < n,
      (encElem (List.courseOfValuesVal step i)).length ≤ elemBound n) :
    ComputableInPolyTime (List.courseOfValues step) encUnary (encList encElem) :=
  courseOfValuesWith (par := fun _ : ℕ => false) (count := id) (step := fun _ => step)
    (const false) id' (hstep.comp (snd encBool (encList encElem)))
    (PolyBounded.of_polynomiallyBounded (fun n : ℕ => (encUnary n).length) hbound)
    fun n i hi => by
      simpa only [encUnary_apply, List.length_replicate] using helem n i hi

/-- **Course-of-values value from unary stage `n`** on framed lists. -/
theorem courseOfValuesVal {β : Type} {encElem : β ↪ List Bool} {step : List β → β}
    (hstep : ComputableInPolyTime step (encList encElem) encElem)
    {elemBound : ℕ → ℕ} (hbound : PolynomiallyBounded elemBound)
    (helem : ∀ n, ∀ i < n,
      (encElem (List.courseOfValuesVal step i)).length ≤ elemBound n) :
    ComputableInPolyTime (List.courseOfValuesVal step) encUnary encElem :=
  hstep.comp (courseOfValues hstep hbound helem)

/-- **Course-of-values certificate for raw Boolean tables (`encBits`)** with a captured parameter
`par` and unary stage count `count`. No explicit element bound is needed because every stage appends
one bit. -/
theorem bitsCourseOfValuesWith {γ π : Type}
    {encIn : γ ↪ List Bool} {encPar : π ↪ List Bool}
    {par : γ → π} {count : γ → ℕ} {step : π → List Bool → Bool}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : π × List Bool => step p.1 p.2)
      (encPair encPar encBits) encBool) :
    ComputableInPolyTime (fun x => List.courseOfValues (step (par x)) (count x)) encIn encBits :=
  courseOfValuesWith_of_tableBound hpar hcount hstep bitsSnoc hcount.polyBounded fun x i hi => by
    change (List.courseOfValues (step (par x)) i).length ≤ count x
    rw [List.length_courseOfValues]
    exact hi

/-- **Course-of-values certificate for raw Boolean tables (`encBits`) from unary stage `n`.**
No explicit element bound is needed because every stage appends one bit. -/
theorem bitsCourseOfValues {step : List Bool → Bool}
    (hstep : ComputableInPolyTime step encBits encBool) :
    ComputableInPolyTime (List.courseOfValues step) encUnary encBits :=
  bitsCourseOfValuesWith (par := fun _ : ℕ => false) (count := id) (step := fun _ => step)
    (const false) id' (hstep.comp (snd encBool encBits))

/-- **Course-of-values Boolean value on `encBits` from unary stage `n`.** -/
theorem bitsCourseOfValuesVal {step : List Bool → Bool}
    (hstep : ComputableInPolyTime step encBits encBool) :
    ComputableInPolyTime (List.courseOfValuesVal step) encUnary encBool :=
  hstep.comp (bitsCourseOfValues hstep)

end Turing.MultiTapeTM.ComputableInPolyTime
