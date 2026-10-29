/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Planar.CrossoverSplit

/-!
# Unique extensions through the fixed crossover

The fixed clause tables have exactly one satisfying full assignment for each pair of incoming
bits. The explicit Boolean extension and its uniqueness are preserved by the internal splitting
rings. Construction and source credit are documented in `Crossover` and `CrossoverSplit`.

## Main definitions

* `Cslib.Logic.PL.CNF.Crossover.canonicalExtension`: the original full assignment from two bits.
* `Cslib.Logic.PL.CNF.Crossover.canonicalSplitExtension`: its lift to all internal copies.

## Main results

* `Cslib.Logic.PL.CNF.Crossover.existsUnique_holds`: uniqueness before splitting.
* `Cslib.Logic.PL.CNF.Crossover.existsUnique_split_holds`: uniqueness after splitting.

## References

The construction adapts [Lichtenstein1982, Figs. 4–5] and [Tromino2025, Fig. 8(b)].
Unique extension is the parsimony condition of
[HuntMaratheRadhakrishnanStearns1998, Definition 3.1]. Their Theorem 3.2 proves that property for
Lichtenstein's crossover; kernel evaluation checks the adapted 13-variable table here.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Crossover

/-- The full satisfying assignment determined by the left and top input values.
The explicit Boolean expressions describe all nine internal values as well as the outputs. -/
def canonicalExtension (a b : Bool) : Variable → Bool :=
  assignment a a b b a (!a || b) (!a || !b) b a b (a || b) (a || !b) a

/-- The explicit extension satisfies all 26 clauses for every pair of inputs. -/
theorem eval_canonicalExtension (a b : Bool) :
    formula.eval (canonicalExtension a b) = true := by
  cases a <;> cases b <;> decide +kernel

-- Only the nine internal values are enumerated after the two inputs are fixed; the existing
-- boundary theorem has already identified the outputs with those inputs.
private theorem assignment_eq_canonicalExtension (a b : Bool) :
    ∀ aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
        upperRight lowerRight aInnerRight : Bool,
      formula.eval (assignment a a b b aInnerLeft upperLeft lowerLeft bInnerTop center
        bInnerBottom upperRight lowerRight aInnerRight) = true →
      ∀ v, assignment a a b b aInnerLeft upperLeft lowerLeft bInnerTop center
        bInnerBottom upperRight lowerRight aInnerRight v = canonicalExtension a b v := by
  cases a <;> cases b <;> decide +kernel

/-- Every satisfying full assignment is the explicit extension of its two incoming values. -/
theorem eq_canonicalExtension_of_holds {σ : Variable → Bool}
    (h : formula.eval σ = true) :
    σ = canonicalExtension (σ .aLeft) (σ .bTop) := by
  obtain ⟨horizontal, vertical⟩ := boundary_eq_of_holds h
  have heq : assignment (σ .aLeft) (σ .aLeft) (σ .bTop) (σ .bTop)
      (σ .aInnerLeft) (σ .upperLeft) (σ .lowerLeft) (σ .bInnerTop) (σ .center)
      (σ .bInnerBottom) (σ .upperRight) (σ .lowerRight) (σ .aInnerRight) = σ := by
    funext v
    cases v <;> first | rfl | exact horizontal | exact vertical
  have hfull := assignment_eq_canonicalExtension (σ .aLeft) (σ .bTop)
    (σ .aInnerLeft) (σ .upperLeft) (σ .lowerLeft) (σ .bInnerTop) (σ .center)
    (σ .bInnerBottom) (σ .upperRight) (σ .lowerRight) (σ .aInnerRight)
  rw [heq] at hfull
  exact funext (hfull h)

/-- Satisfying assignments agreeing on the incoming ports agree on every variable. -/
theorem ext_of_holds {σ τ : Variable → Bool}
    (hσ : formula.eval σ = true) (hτ : formula.eval τ = true)
    (ha : σ .aLeft = τ .aLeft) (hb : σ .bTop = τ .bTop) : σ = τ := by
  rw [eq_canonicalExtension_of_holds hσ, eq_canonicalExtension_of_holds hτ, ha, hb]

/-- Each pair of incoming values extends uniquely to a satisfying full assignment. -/
theorem existsUnique_holds (a b : Bool) :
    ∃! σ : Variable → Bool,
      formula.eval σ = true ∧ σ .aLeft = a ∧ σ .bTop = b := by
  refine ⟨canonicalExtension a b, ⟨eval_canonicalExtension a b, rfl, rfl⟩, ?_⟩
  rintro σ ⟨hσ, ha, hb⟩
  rw [eq_canonicalExtension_of_holds hσ, ha, hb]

/-- The explicit full split assignment: every local copy receives its original variable's
canonical value, determined by the left and top inputs. -/
def canonicalSplitExtension (a b : Bool) : SplitVariable → Bool :=
  canonicalExtension a b ∘ SplitVariable.origin

/-- The canonical split extension satisfies all 74 clauses. -/
theorem eval_canonicalSplitExtension (a b : Bool) :
    splitFormula.eval (canonicalSplitExtension a b) = true :=
  eval_splitFormula_lift _ (eval_canonicalExtension a b)

/-- Every satisfying split assignment is the explicit extension of its incoming values.
The implication rings identify the six copies before applying the original uniqueness result;
no enumeration of assignments to the 53 split variables is needed. -/
theorem eq_canonicalSplitExtension_of_holds {σ : SplitVariable → Bool}
    (h : splitFormula.eval σ = true) :
    σ = canonicalSplitExtension (σ .aLeft) (σ .bTop) := by
  obtain ⟨hbase, hagree⟩ := (eval_splitFormula_iff σ).1 h
  have heq := eq_canonicalExtension_of_holds hbase
  funext v
  have hv := congrFun heq v.origin
  cases v with
  | aLeft | aRight | bTop | bBottom | center => exact hv
  | copy v i =>
    have hzero : σ (.copy v 0) = canonicalSplitExtension (σ .aLeft) (σ .bTop)
        (.copy v i) := by
      cases v <;> exact hv
    exact (hagree v i).trans hzero

/-- Satisfying split assignments agreeing on the two incoming ports agree everywhere. -/
theorem split_ext_of_holds {σ τ : SplitVariable → Bool}
    (hσ : splitFormula.eval σ = true) (hτ : splitFormula.eval τ = true)
    (ha : σ .aLeft = τ .aLeft) (hb : σ .bTop = τ .bTop) : σ = τ := by
  rw [eq_canonicalSplitExtension_of_holds hσ, eq_canonicalSplitExtension_of_holds hτ, ha, hb]

/-- Each pair of incoming values extends uniquely to a satisfying full split assignment. -/
theorem existsUnique_split_holds (a b : Bool) :
    ∃! σ : SplitVariable → Bool,
      splitFormula.eval σ = true ∧ σ .aLeft = a ∧ σ .bTop = b := by
  refine ⟨canonicalSplitExtension a b, ⟨eval_canonicalSplitExtension a b, rfl, rfl⟩, ?_⟩
  rintro σ ⟨hσ, ha, hb⟩
  rw [eq_canonicalSplitExtension_of_holds hσ, ha, hb]

end Cslib.Logic.PL.CNF.Crossover
