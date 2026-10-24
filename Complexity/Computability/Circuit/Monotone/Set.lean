/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Basic
public import Complexity.Computability.Circuit.SourceComplexity
public import Mathlib.Data.Set.BoolIndicator

/-!
# Monotone circuits constructing sets

The existing monotone signature acts on sets by intersection and union. Its constants denote
the empty and full sets. Native `Program` and `Circuit` supply the syntax, evaluation and costs;
the interpretation does not require decidable membership or a finite ambient type.

Mathlib's Boolean characteristic functions turn pointwise membership into an interpretation
homomorphism. Constructing a tuple of sets is equivalent to computing its membership functions
from those of the supplied sets, using exactly the same circuit. Thus arbitrary operation
weights, sharing, unused gates and all designated outputs are preserved. The characteristic
functions are noncomputable for arbitrary sets; this is a semantic correspondence.

## Main definitions

* `Cslib.Circuits.Monotone.setInterpretation`: sets as an interpretation of the monotone basis.
* `Cslib.Circuits.Monotone.membershipHomomorphism`: pointwise Boolean membership.

## Main results

* `Cslib.Circuits.Monotone.eval_set_iff_computesFrom`: set construction is pointwise computation.
* `Cslib.Circuits.Monotone.eval_setOf_iff_computesFrom`: the interface for Boolean source families.
* `Cslib.Circuits.Monotone.ecomplexityFrom_boolIndicator`: equality of weighted complexities.

## References

* Adapted from Basis/AndOr.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic],
  extending its binary AND/OR interpretation to the existing basis with constants.
  The pointwise interface adapts LowerBound/Fusion/Boolean.lean from the same source.
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

variable {U : Type*} {n m : ℕ}

/-- Interpret conjunction and disjunction as intersection and union, with empty/full constants. -/
def setInterpretation (U : Type*) : Interpretation signature (Set U)
  | .const false, _ => ∅
  | .const true, _ => Set.univ
  | .and, args => args 0 ∩ args 1
  | .or, args => args 0 ∪ args 1

/-- Evaluating `.const false` under `setInterpretation` gives the empty set. -/
@[simp] theorem setInterpretation_false (U : Type*) (args : Fin 0 → Set U) :
    setInterpretation U (.const false) args = ∅ := rfl

/-- Evaluating `.const true` under `setInterpretation` gives the full set `Set.univ`. -/
@[simp] theorem setInterpretation_true (U : Type*) (args : Fin 0 → Set U) :
    setInterpretation U (.const true) args = Set.univ := rfl

/-- Evaluating `.and` under `setInterpretation` intersects the two argument sets. -/
@[simp] theorem setInterpretation_and {U : Type*} (args : Fin 2 → Set U) :
    setInterpretation U .and args = args 0 ∩ args 1 := rfl

/-- Evaluating `.or` under `setInterpretation` takes the union of the two argument sets. -/
@[simp] theorem setInterpretation_or {U : Type*} (args : Fin 2 → Set U) :
    setInterpretation U .or args = args 0 ∪ args 1 := rfl

/-- Every set operation is monotone in its arguments. -/
theorem setInterpretation_mono (op : Op) :
    Monotone (setInterpretation U op) := by
  intro a b h
  cases op with
  | const value => cases value <;> exact Set.Subset.rfl
  | and => exact Set.inter_subset_inter (h 0) (h 1)
  | or => exact Set.union_subset_union (h 0) (h 1)

/-- Membership at a point commutes with all operations, including the empty/full constants. -/
noncomputable def membershipHomomorphism (x : U) :
    Homomorphism (setInterpretation U) interpretation where
  map s := s.boolIndicator x
  homomorphic op args := by
    cases op with
    | const b => cases b <;> simp [Set.boolIndicator, setInterpretation, interpretation]
    | and | or =>
      apply Bool.eq_iff_iff.mpr
      simp only [setInterpretation, interpretation, Function.comp_apply, Bool.and_eq_true,
        Bool.or_eq_true, ← Set.mem_iff_boolIndicator, Set.mem_inter_iff, Set.mem_union]

/-- `membershipHomomorphism x` maps a set `s` to `s.boolIndicator x`. -/
@[simp] theorem membershipHomomorphism_map (x : U) (s : Set U) :
    (membershipHomomorphism x).map s = s.boolIndicator x := rfl

/-- Constructing all target sets is equivalent to computing their characteristic functions
from those of the supplied sets. This retains the circuit and every designated output. -/
theorem eval_set_iff_computesFrom (c : Circuit signature n m) (input : Fin n → Set U)
    (target : Fin m → Set U) :
    c.eval (setInterpretation U) input = target ↔
      c.ComputesFrom interpretation (fun x o => (target o).boolIndicator x)
        (fun x i => (input i).boolIndicator x) := by
  constructor
  · intro h x
    exact (c.map_eval (membershipHomomorphism x) input).symm.trans (congrArg _ h)
  · intro h
    funext o
    ext x
    have hp := congrFun ((c.map_eval (membershipHomomorphism x) input).trans (h x)) o
    change (c.eval (setInterpretation U) input o).boolIndicator x =
      (target o).boolIndicator x at hp
    rw [Set.mem_iff_boolIndicator, Set.mem_iff_boolIndicator, hp]

/-- Boolean source families may be given directly as ordinary functions, with their true sets
as the set-valued inputs. In particular, sources may include positive and negative literals. -/
theorem eval_setOf_iff_computesFrom (c : Circuit signature n m) (sources : U → Fin n → Bool)
    (target : U → Fin m → Bool) :
    c.eval (setInterpretation U) (fun i => {x | sources x i = true}) =
      (fun o => {x | target x o = true}) ↔ c.ComputesFrom interpretation target sources := by
  simpa [Set.boolIndicator] using
    eval_set_iff_computesFrom c (fun i => {x | sources x i = true})
      (fun o => {x | target x o = true})

/-- Pointwise Boolean computation and constructing the fixed tuple of sets have equal minimum
cost for every operation weight, including infinity when no circuit exists. -/
theorem ecomplexityFrom_boolIndicator (weight : Op → ℕ) (input : Fin n → Set U)
    (target : Fin m → Set U) :
    ecomplexityFrom interpretation weight (fun x o => (target o).boolIndicator x)
      (fun x i => (input i).boolIndicator x) =
        ecomplexityFrom (setInterpretation U) weight (fun _ : Unit => target)
          (fun _ : Unit => input) := by
  simp only [ecomplexityFrom, iInf_subtype, ← eval_set_iff_computesFrom]
  simp only [Circuit.ComputesFrom, forall_const]

end Cslib.Circuits.Monotone
