/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Completeness
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Size
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Syntax

/-!
# Parsimonious occurrence reduction for 3SAT

The existing occurrence splitter preserves the number of satisfying assignments. Each source
variable has one value on every copy in its implication cycle, and numbering copies is injective.
The counting problems below count only occurring variables and return zero outside their syntax.
They reuse `CNF.modelCount` and the existing syntax guards rather than introducing new assignment
or satisfiability semantics.

## Main definitions

* `Cslib.Complexity.SharpThreeSAT`: model count for width-at-most-three CNF, zero otherwise.
* `Cslib.Complexity.SharpThreeSATThree`: model count with the additional three-occurrence bound.

## Main results

* `Cslib.Complexity.sharpThreeSATThree_toThreeSATThree`: exact counts for the total compiler.
* `Cslib.Complexity.parsimoniousReducible_SharpThreeSAT_SharpThreeSATThree`: the existing
  polynomial-time compiler is a parsimonious reduction.

## References

The occurrence construction and its source credit are documented in `ThreeSATThree`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- Count satisfying assignments of width-at-most-three CNF; reject other syntax with count zero.
Only variables occurring in the formula are counted. -/
def SharpThreeSAT (φ : CNF ℕ) : ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then φ.modelCount else 0

/-- Count satisfying assignments of width-three, occurrence-three CNF; reject other syntax with
count zero. Repetitions are literal positions, as in `ThreeSATThree.syntaxCheck`. -/
def SharpThreeSATThree (φ : CNF ℕ) : ℕ :=
  if ThreeSATThree.syntaxCheck φ then φ.modelCount else 0

/-- The total occurrence compiler preserves the count, including rejected inputs. -/
theorem sharpThreeSATThree_toThreeSATThree (φ : CNF ℕ) :
    SharpThreeSATThree (toThreeSATThree φ) = SharpThreeSAT φ := by
  have hout := (ThreeSATThree.syntaxCheck_iff (toThreeSATThree φ)).2
    ⟨width_toThreeSATThree φ, count_vars_toThreeSATThree_le φ⟩
  simp only [SharpThreeSATThree, hout, ↓reduceIte]
  by_cases hw : φ.all (fun c => decide (c.length ≤ 3)) = true
  · have hwidth : ∀ c ∈ φ, c.length ≤ 3 := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hw
    rw [modelCount_toThreeSATThree φ hwidth]
    simp only [SharpThreeSAT, hw, ↓reduceIte]
  · simp only [SharpThreeSAT, toThreeSATThree, hw, Bool.false_eq_true, ite_false]
    decide

/-- The already-certified polynomial-time 3SAT-to-3SAT-3 compiler is parsimonious. -/
theorem parsimoniousReducible_SharpThreeSAT_SharpThreeSATThree :
    ParsimoniousReducible encCNF encCNF SharpThreeSAT SharpThreeSATThree :=
  ⟨toThreeSATThree, computableInPolyTime_toThreeSATThree,
    fun φ => (sharpThreeSATThree_toThreeSATThree φ).symm⟩

end Cslib.Complexity
