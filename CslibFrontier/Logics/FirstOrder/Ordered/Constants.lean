/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Interpretation
public import CslibFrontier.Logics.FirstOrder.Interpretation.Constants

/-!
# Canonical constants as interpreted target symbols

The canonical source expansion defines target constants `0`, `1` and `max` by equality to the
corresponding source terms. These definitions satisfy the existence/uniqueness requirement for
every canonical `Fin n` structure with `n ≥ 2`. Thus the native constant-aware pullback applies
to all formulas of the input relational vocabulary expanded by these three target constants.

This supplies target constants in the semantic interpretation API. Native full-tuple BIT is
constructed separately in `Ordered.TupleBit`, and numeric-preserving composition in
`Ordered.FullTuple.Composition` and `Ordered.DomainInterpretation.Composition`. Ordered
logspace and machine-capture results remain separate.

## Main definitions

* `Cslib.Logic.FO.Ordered.constants`: canonical definitions of the three target constants.

## Main results

* `Cslib.Logic.FO.Ordered.constants_valid`: the definitions are valid for every `n ≥ 2`.
* `Cslib.Logic.FO.Ordered.constants_value_val`: the selected values are the canonical indices.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 1.2 and Proposition 3.5.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- Define the target constants by equality to the canonical source constants. -/
def constants (L : Language) : (forget L).WithConstants (NumericFunction 0) where
  constant c := Term.equal (.var ())
    (.func ((LHom.sumInr : numericLanguage →ᴸ language L).onFunction c) Fin.elim0)

variable {L : Language} [L.IsRelational] {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- Every canonical constant defines exactly one tuple in the forgetting interpretation. -/
theorem constants_valid : (constants L).Valid (Fin n) := by
  intro c
  let x : Fin n := (numericStructure (n := n) Fact.out).funMap c Fin.elim0
  refine ⟨forgetEquiv.symm x, ?_, ?_⟩
  · simp only [constants, Formula.realize_equal, Term.realize_var, Term.realize_func]
    cases c <;> rfl
  · intro y hy
    simp only [constants, Formula.realize_equal, Term.realize_var, Term.realize_func] at hy
    apply Interpretation.Model.ext
    funext i
    cases i
    cases c <;> exact hy

/-- The selected target constants have indices zero, one and `n - 1`, respectively. -/
theorem constants_value_val (c : NumericFunction 0) :
    (((constants L).value (constants_valid (n := n)) c).val ()).val = c.index n := by
  have h := (constants L).value_spec (constants_valid (L := L) (n := n)) c
  simp only [constants, Formula.realize_equal, Term.realize_var, Term.realize_func] at h
  exact congrArg Fin.val h

end Cslib.Logic.FO.Ordered
