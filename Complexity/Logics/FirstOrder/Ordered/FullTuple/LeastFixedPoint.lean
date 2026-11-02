/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.FullTuple
public import Complexity.Logics.FirstOrder.Ordered.LeastFixedPoint
public import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint.Tuple.Semantics

/-!
# Ordered full-tuple interpretations preserve least-fixed-point definability

The ordinary full-tuple interpretation, with its native canonical order, BIT, and constants,
extends to checked FO(LFP) formulas. Each target relation argument is replaced by a coordinate
block; positivity and nested binding are preserved. The sentence pullback has exactly the
truth value of the original sentence on the canonical rank universe.

## References

* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Section 3:
  polynomial-sized tableau domains are represented by tuples over the input structure.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

variable {L L' : Language} [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k)

/-- Pull back checked FO(LFP) syntax, multiplying every relation arity by the tuple dimension. -/
noncomputable def onLFPFormula {Γ : List ℕ} {α : Type}
    (φ : LFP.Formula (language L') Γ α) :
    LFP.Formula (language L) (Γ.map (· * k)) (α × Fin k) :=
  ⟨LFP.Tuple.onFormula I.onFormula φ.val, by
    rw [LFP.Tuple.wellFormed_onFormula]
    exact φ.property⟩

/-- Pull back a checked sentence; its empty free-variable context remains empty. -/
noncomputable def onLFPSentence (φ : LFP.Formula (language L') [] Empty) :
    LFP.Formula (language L) [] Empty :=
  ⟨(I.onLFPFormula φ).val.relabel Prod.fst, by
    rw [Operator.Formula.wellFormed_relabel]
    exact (I.onLFPFormula φ).property⟩

variable {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The sentence pullback preserves truth on the canonical lexicographically ranked universe. -/
theorem realize_onLFPSentence (hk : 0 < k) (φ : LFP.Formula (language L') [] Empty) :
    (I.onLFPSentence φ).Realize (M := Fin n) Operator.RelEnv.empty Empty.elim ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      φ.Realize (M := Fin (n ^ k)) Operator.RelEnv.empty Empty.elim := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  have hf {α : Type} (ψ : (language L').Formula α) (v : α × Fin k → Fin n) :
      (I.onFormula ψ).Realize v ↔
        ψ.Realize (M := Fin (n ^ k)) (fun a => lexEquiv (fun i => v (a, i))) :=
    I.realize_onFormula hk ψ (fun a i => v (a, i))
  simp only [onLFPSentence, LFP.Formula.Realize, onLFPFormula,
    Operator.Formula.realize_relabel]
  have h := LFP.Tuple.realize_onFormula I.onFormula lexEquiv hf φ.val
    Operator.RelEnv.empty Operator.RelEnv.empty (fun {_} r => nomatch r)
    (Empty.elim ∘ Prod.fst)
  convert h using 1
  exact iff_of_eq (congrArg (φ.val.Realize LFP.interpretation Operator.RelEnv.empty)
    (Subsingleton.elim _ _))

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
