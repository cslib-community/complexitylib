/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P

/-!
# Promise problems

A promise problem is a pair of disjoint sets of instances, the yes-instances and the no-instances
[Even, Selman and Yacobi][EvenSelmanYacobi1984], [Goldreich][Goldreich2006]. An instance in
neither set is outside the promise, and an algorithm solving the problem may answer anything on
it. A decision problem `A : Set α` is the promise problem whose yes-instances are `A` and whose
no-instances are `Aᶜ` (`PromiseProblem.ofSet`).

A class `C` of decision problems lifts to promise problems through completions:
`promiseClass C` consists of the promise problems separated by some problem in `C`, one that
contains every yes-instance and no no-instance. `PromiseP enc` and `PromiseNP enc` are the lifts
of `P enc` and `NP enc`, and they agree with Goldreich's definitions by polynomial-time algorithms
and verifiers that are only constrained on the promise (`mem_PromiseP_iff`, `mem_PromiseNP_iff`).
A decision problem is in a lifted class exactly when it is in the class
(`ofSet_mem_promiseClass`), so lifting is injective, and `PromiseP enc = PromiseNP enc` exactly
when `P enc = NP enc` (`PromiseP_eq_PromiseNP_iff`).

## Main definitions

* `Cslib.Complexity.PromiseProblem`, with the complement `Qᶜ` exchanging the yes-instances and
  the no-instances.
* `Cslib.Complexity.PromiseProblem.ofSet`: a decision problem as a promise problem.
* `Cslib.Complexity.PromiseProblem.SolvedBy`: a Boolean function solves a promise problem.
* `Cslib.Complexity.promiseClass`: the lift of a class of decision problems.
* `Cslib.Complexity.PromiseP`, `Cslib.Complexity.PromiseNP`.

## Main results

* `Cslib.Complexity.ofSet_mem_promiseClass`, `Cslib.Complexity.promiseClass_inj`: lifting
  reflects membership and equality of classes.
* `Cslib.Complexity.mem_promiseClass_iff_solvedBy`: the lift of a class defined by deciding
  functions consists of the promise problems solved by such functions.
* `Cslib.Complexity.mem_PromiseP_iff`, `Cslib.Complexity.mem_PromiseNP_iff`: Goldreich's
  definitions.
* `Cslib.Complexity.PromiseP_eq_PromiseNP_iff`: `PromiseP = PromiseNP ↔ P = NP`.

## References

* [S. Even, A. Selman, Y. Yacobi, *The complexity of promise problems with applications to
  public-key cryptography*][EvenSelmanYacobi1984]
* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A promise problem: disjoint sets of yes-instances and no-instances. Instances in neither set
are outside the promise. -/
@[ext]
structure PromiseProblem (α : Type*) where
  /-- The instances on which the answer must be yes. -/
  yes : Set α
  /-- The instances on which the answer must be no. -/
  no : Set α
  /-- No instance is both a yes-instance and a no-instance. -/
  disjoint : Disjoint yes no

namespace PromiseProblem

variable {α : Type*} {Q : PromiseProblem α} {A : Set α} {f : α → Bool}

/-- The promise: the instances that are yes-instances or no-instances. -/
def promise (Q : PromiseProblem α) : Set α := Q.yes ∪ Q.no

/-- `f` solves `Q` when it answers `true` on the yes-instances and `false` on the no-instances;
its answers outside the promise do not matter. -/
def SolvedBy (Q : PromiseProblem α) (f : α → Bool) : Prop :=
  (∀ a ∈ Q.yes, f a = true) ∧ ∀ a ∈ Q.no, f a = false

/-- A decision problem as a promise problem: every instance is in the promise. -/
def ofSet (A : Set α) : PromiseProblem α := ⟨A, Aᶜ, disjoint_compl_right⟩

/-- The complement of a promise problem exchanges its yes-instances and its no-instances. -/
instance : Compl (PromiseProblem α) := ⟨fun Q => ⟨Q.no, Q.yes, Q.disjoint.symm⟩⟩

@[simp] theorem yes_compl : Qᶜ.yes = Q.no := rfl

@[simp] theorem no_compl : Qᶜ.no = Q.yes := rfl

@[simp] theorem compl_compl : Qᶜᶜ = Q := rfl

@[simp] theorem yes_ofSet : (ofSet A).yes = A := rfl

@[simp] theorem no_ofSet : (ofSet A).no = Aᶜ := rfl

@[simp] theorem promise_ofSet : (ofSet A).promise = Set.univ := Set.union_compl_self A

theorem ofSet_compl : ofSet Aᶜ = (ofSet A)ᶜ := by
  ext <;> simp

/-- A function solves the complement of a promise problem when its negation solves the problem. -/
theorem solvedBy_compl : Qᶜ.SolvedBy f ↔ Q.SolvedBy fun a => !f a := by
  simp only [SolvedBy, Bool.not_eq_true', Bool.not_eq_false']
  exact and_comm

/-- A function solves a decision problem when it decides it. -/
theorem solvedBy_ofSet : (ofSet A).SolvedBy f ↔ ∀ a, a ∈ A ↔ f a = true := by
  simp only [SolvedBy, yes_ofSet, no_ofSet, Set.mem_compl_iff, Bool.eq_false_iff]
  exact ⟨fun h a => ⟨h.1 a, not_imp_not.1 (h.2 a)⟩, fun h => ⟨fun a => (h a).1,
    fun a => mt (h a).2⟩⟩

end PromiseProblem

open PromiseProblem

/-! ### Lifting classes of decision problems -/

section promiseClass

variable {α : Type*} {C D : Set (Set α)} {Q : PromiseProblem α}

/-- The lift of a class `C` of decision problems to promise problems: the promise problems
separated by a problem in `C`, which contains every yes-instance and no no-instance. -/
def promiseClass (C : Set (Set α)) : Set (PromiseProblem α) :=
  {Q | ∃ A ∈ C, Q.yes ⊆ A ∧ Disjoint A Q.no}

theorem mem_promiseClass : Q ∈ promiseClass C ↔ ∃ A ∈ C, Q.yes ⊆ A ∧ Disjoint A Q.no := Iff.rfl

theorem promiseClass_mono : Monotone (promiseClass (α := α)) :=
  fun _ _ hCD _ ⟨A, hA, hyes, hno⟩ => ⟨A, hCD hA, hyes, hno⟩

/-- A decision problem is in the lift of a class exactly when it is in the class. -/
@[simp] theorem ofSet_mem_promiseClass {A : Set α} : ofSet A ∈ promiseClass C ↔ A ∈ C := by
  refine ⟨fun ⟨B, hB, hAB, hBA⟩ => ?_, fun hA => ⟨A, hA, subset_rfl, disjoint_compl_right⟩⟩
  obtain rfl : B = A := (Set.disjoint_compl_right_iff_subset.1 hBA).antisymm hAB
  exact hB

theorem promiseClass_subset_promiseClass_iff : promiseClass C ⊆ promiseClass D ↔ C ⊆ D :=
  ⟨fun h _ hA => ofSet_mem_promiseClass.1 (h (ofSet_mem_promiseClass.2 hA)),
    fun h => promiseClass_mono h⟩

theorem promiseClass_injective : Function.Injective (promiseClass (α := α)) := fun _ _ h =>
  (promiseClass_subset_promiseClass_iff.1 h.le).antisymm
    (promiseClass_subset_promiseClass_iff.1 h.ge)

/-- Two classes of decision problems have the same lift to promise problems exactly when they are
equal. -/
theorem promiseClass_inj : promiseClass C = promiseClass D ↔ C = D :=
  promiseClass_injective.eq_iff

/-- If a class is closed under complement, so is its lift. -/
theorem compl_mem_promiseClass (hC : ∀ A ∈ C, Aᶜ ∈ C) (hQ : Q ∈ promiseClass C) :
    Qᶜ ∈ promiseClass C :=
  let ⟨A, hA, hyes, hno⟩ := hQ
  ⟨Aᶜ, hC A hA, Set.subset_compl_iff_disjoint_left.2 hno,
    Set.disjoint_compl_left_iff_subset.2 hyes⟩

/-- If the problems in `C` are those decided by the functions satisfying `Good`, then the lift of
`C` consists of the promise problems solved by such functions. -/
theorem mem_promiseClass_iff_solvedBy {Good : (α → Bool) → Prop}
    (hC : ∀ A, A ∈ C ↔ ∃ f, Good f ∧ ∀ a, a ∈ A ↔ f a = true) :
    Q ∈ promiseClass C ↔ ∃ f, Good f ∧ Q.SolvedBy f := by
  constructor
  · rintro ⟨A, hA, hyes, hno⟩
    obtain ⟨f, hf, hA⟩ := (hC A).1 hA
    refine ⟨f, hf, fun a ha => (hA a).1 (hyes ha), fun a ha => ?_⟩
    rw [← Bool.not_eq_true, ← hA a]
    exact Set.disjoint_right.1 hno ha
  · rintro ⟨f, hf, hyes, hno⟩
    refine ⟨{a | f a = true}, (hC _).2 ⟨f, hf, fun _ => Iff.rfl⟩, fun a ha => hyes a ha, ?_⟩
    exact Set.disjoint_right.2 fun a ha h => by simp [hno a ha] at h

end promiseClass

/-! ### Promise-P and promise-NP -/

section PromiseP

variable {α : Type*} {enc : α ↪ List Bool} {Q : PromiseProblem α}

/-- The promise problems solved by polynomial-time algorithms, with respect to the encoding `enc`
of instances: the lift of `P enc` [Goldreich][Goldreich2006]. -/
def PromiseP (enc : α ↪ List Bool) : Set (PromiseProblem α) := promiseClass (P enc)

/-- **Goldreich's definition of promise-P**: a promise problem is in `PromiseP` when a
polynomial-time function solves it. -/
theorem mem_PromiseP_iff :
    Q ∈ PromiseP enc ↔ ∃ f : α → Bool, ComputableInPolyTime f enc encBool ∧ Q.SolvedBy f :=
  mem_promiseClass_iff_solvedBy fun _ => mem_P

@[simp] theorem ofSet_mem_PromiseP {A : Set α} : ofSet A ∈ PromiseP enc ↔ A ∈ P enc :=
  ofSet_mem_promiseClass

end PromiseP

section PromiseNP

variable {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α}

/-- The promise problems with polynomial-time verifiers, with respect to the encoding `enc` of
instances: the lift of `NP enc` [Goldreich][Goldreich2006]. -/
def PromiseNP (enc : α ↪ List Bool) : Set (PromiseProblem α) := promiseClass (NP enc)

/-- **Goldreich's definition of promise-NP**: a promise problem is in `PromiseNP` when a
polynomial-time verifier accepts some certificate for every yes-instance and none for any
no-instance. -/
theorem mem_PromiseNP_iff : Q ∈ PromiseNP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a ∈ Q.yes, ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true) ∧
      ∀ a ∈ Q.no, ∀ w : List Bool, w.length = p.eval (enc a).length → V (a, w) = false := by
  have this : Q ∈ PromiseNP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a ∈ Q.yes, ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true) ∧ ∀ a ∈
      Q.no, ∀ w : List Bool, w.length = p.eval (enc a).length → V (a, w) = false := by
    constructor
    · rintro ⟨A, ⟨p, V, hV, h⟩, hyes, hno⟩
      refine ⟨p, V, hV.tidy, fun a ha => (h a).1 (hyes ha), fun a ha w hw => ?_⟩
      rw [← Bool.not_eq_true]
      exact fun hVw => Set.disjoint_right.1 hno ha ((h a).2 ⟨w, hw, hVw⟩)
    · rintro ⟨p, V, hV, hyes, hno⟩
      refine ⟨{a | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true},
        ⟨p, V, .of_tidy hV, fun _ => Iff.rfl⟩, hyes, Set.disjoint_right.2 fun a ha ⟨w, hw, hVw⟩ =>
          ?_⟩
      simp [hno a ha w hw] at hVw
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

@[simp] theorem ofSet_mem_PromiseNP {A : Set α} : ofSet A ∈ PromiseNP enc ↔ A ∈ NP enc :=
  ofSet_mem_promiseClass

/-- **`PromiseP = PromiseNP ↔ P = NP`.** -/
theorem PromiseP_eq_PromiseNP_iff : PromiseP enc = PromiseNP enc ↔ P enc = NP enc :=
  promiseClass_inj

end PromiseNP

end Cslib.Complexity
