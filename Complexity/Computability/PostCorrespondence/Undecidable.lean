/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.SingleTape.TM0Universal
public import Complexity.Computability.PostCorrespondence.Modified
public import Complexity.Computability.PostCorrespondence.OfTM0
public import Complexity.Computability.PostCorrespondence.Substitution
public import Mathlib.Computability.Halting

/-!
# Undecidability of Post's correspondence problem

**Post's correspondence problem is undecidable** [Post1946]; [Sipser2013, Theorem 5.15]: no
computable predicate decides whether a list of dominoes over `Bool`, or over any alphabet with two
distinct letters, has a match (`not_computablePred_solvable_bool`, `not_computablePred_solvable`).
The modified problem MPCP is undecidable too (`not_computablePred_mSolvable_bool`,
`not_computablePred_mSolvable`).

The reduction is from the halting problem for Mathlib's partial recursive codes,
`ComputablePred.halting_problem`. We use the universal `TM0` machine `M₀'` with finitely many
states and symbols (`Turing.TM0.Universal.M₀'`). A code `c` halts on `0` iff `M₀'` halts on the
input tape `input (encode c)`, iff the MPCP instance `OfTM0.mInstance M₀' (input (encode c))` is
solvable. The binary code `boolCode` takes the instance to `Bool`, and `toPCP` from MPCP to PCP;
every step is primitive recursive.

**Scope.** Sipser reduces from the acceptance problem of Turing machines, building the instance
from the machine and its input. Here the machine is fixed: the instance is built from the input
of one universal `TM0` machine, which is how the reduction is computable for Mathlib's codes.

## Main definitions

* `Cslib.PostCorrespondence.mReduction`: the reduction from halting to MPCP over `Bool`.

## Main results

* `Cslib.PostCorrespondence.halting_manyOneReducible_mSolvable`,
  `Cslib.PostCorrespondence.halting_manyOneReducible_solvable`: the halting problem many-one
  reduces to MPCP and to PCP over `Bool`.
* `Cslib.PostCorrespondence.not_computablePred_solvable_bool`,
  `Cslib.PostCorrespondence.not_computablePred_solvable`: **PCP is undecidable**.
* `Cslib.PostCorrespondence.not_computablePred_mSolvable_bool`,
  `Cslib.PostCorrespondence.not_computablePred_mSolvable`: MPCP is undecidable.

## References

* [E. L. Post, *A variant of a recursively unsolvable problem*][Post1946]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence

open Relation Turing StateTransition TM0.Universal

/-- The many-one reduction from the halting problem to MPCP over `Bool`: simulate `univ` on the
code as an MPCP instance, then code the instance in binary. -/
noncomputable def mReduction (c : Nat.Partrec.Code) : MInstance Bool :=
  (OfTM0.mInstance M₀' (input (Encodable.encode c))).subst boolCode

theorem eval_dom_iff_mReduction_solvable (c : Nat.Partrec.Code) :
    (c.eval 0).Dom ↔ (mReduction c).Solvable := by
  rw [mReduction, MInstance.solvable_subst_iff flatMap_boolCode_injective,
    ← OfTM0.eval_dom_iff_solvable, dom_M₀', univ_spec, Denumerable.ofNat_encode]

theorem primrec_mReduction : Primrec mReduction :=
  ((MInstance.primrec_subst primrec_boolCode).comp
    ((OfTM0.primrec_mInstance M₀').comp (primrec_input.comp Primrec.encode))).of_eq fun _ => rfl

/-! ### Undecidability -/

/-- The halting problem reduces to MPCP over `Bool`. -/
theorem halting_manyOneReducible_mSolvable :
    (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ≤₀ (MInstance.Solvable : MInstance Bool → Prop) :=
  ⟨mReduction, primrec_mReduction.to_comp,
    eval_dom_iff_mReduction_solvable⟩

/-- **MPCP is undecidable** over the binary alphabet. -/
theorem not_computablePred_mSolvable_bool :
    ¬ComputablePred (MInstance.Solvable : MInstance Bool → Prop) := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_mSolvable h)

/-- **MPCP is undecidable** over every alphabet with two distinct letters. -/
theorem not_computablePred_mSolvable {α : Type*} [Primcodable α] {a b : α} (hab : a ≠ b) :
    ¬ComputablePred (MInstance.Solvable : MInstance α → Prop) := fun h =>
  not_computablePred_mSolvable_bool
    (ComputablePred.computable_of_manyOneReducible (mSolvable_bool_manyOneReducible hab) h)

/-- The halting problem reduces to PCP over `Bool`: through MPCP over `Bool`, Sipser's reduction
to PCP over `Marked Bool`, and the binary code. -/
theorem halting_manyOneReducible_solvable :
    (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ≤₀ (Solvable : List (Domino Bool) → Prop) :=
  halting_manyOneReducible_mSolvable.trans
    (mSolvable_manyOneReducible.trans solvable_manyOneReducible_bool)

/-- **Post's correspondence problem is undecidable** over the binary alphabet
[Sipser2013, Theorem 5.15]. -/
theorem not_computablePred_solvable_bool :
    ¬ComputablePred (Solvable : List (Domino Bool) → Prop) := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_solvable h)

/-- **Post's correspondence problem is undecidable** over every alphabet with two distinct
letters. -/
theorem not_computablePred_solvable {α : Type*} [Primcodable α] {a b : α} (hab : a ≠ b) :
    ¬ComputablePred (Solvable : List (Domino α) → Prop) := fun h =>
  not_computablePred_solvable_bool
    (ComputablePred.computable_of_manyOneReducible (solvable_bool_manyOneReducible hab) h)

end Cslib.PostCorrespondence
