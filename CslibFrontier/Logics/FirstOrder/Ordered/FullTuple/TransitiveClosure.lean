/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Tuple

/-!
# Ordered full-tuple interpretations preserve transitive-closure definability

The ordinary full-tuple interpretation, with its native canonical order, BIT and constants,
extends to FO(TC) sentences. A closure over pairs of width-`w` target tuples becomes a closure
over pairs of width-`w * k` source tuples; closure polarity is preserved. The sentence pullback
has exactly the truth value of the original sentence on the canonical rank universe, so a
sentence written over a polynomially larger universe `Fin (n ^ k)` becomes a sentence over the
input universe `Fin n`.

## Main definitions

* `FullTupleInterpretation.onTCSentence`: pull back an FO(TC) sentence.

## Main results

* `FullTupleInterpretation.positive_onTCSentence`: the pullback preserves closure polarity.
* `FullTupleInterpretation.realize_onTCSentence_closureBy`: the pullback preserves truth under
  every closure semantics `TC.Tuple.closureBy T` whose transform commutes with bijections.
* `FullTupleInterpretation.realize_onTCSentence`: the pullback preserves truth.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*][Immerman1987], Section 3: machine
  configurations of logarithmic size are coded by tuples of a fixed number of variables, and
  their reachability is expressed by one transitive closure over those tuples.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

variable {L L' : Language} [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k)

/-- Pull back an FO(TC) sentence, multiplying every closure width by the tuple dimension. -/
noncomputable def onTCSentence (φ : Operator.Formula (language L') TC.shape [] Empty) :
    Operator.Formula (language L) TC.shape [] Empty :=
  (TC.Tuple.onFormula I.onFormula φ).relabel Prod.fst

/-- The sentence pullback preserves the polarity of every closure. -/
@[simp] theorem positive_onTCSentence (φ : Operator.Formula (language L') TC.shape [] Empty)
    (s : Bool) : TC.Positive (I.onTCSentence φ) s ↔ TC.Positive φ s :=
  (TC.positive_relabel _ _ s).trans (TC.Tuple.positive_onFormula _ φ s)

variable {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The sentence pullback preserves truth on the canonical lexicographically ranked universe,
under every closure semantics `TC.Tuple.closureBy T` whose transform commutes with bijections. -/
theorem realize_onTCSentence_closureBy {T : ∀ {β : Type}, (β → β → Prop) → β → β → Prop}
    (hT : TC.Tuple.Transports T) (hk : 0 < k)
    (φ : Operator.Formula (language L') TC.shape [] Empty) :
    (I.onTCSentence φ).Realize (M := Fin n) (TC.Tuple.closureBy T) Operator.RelEnv.empty
        Empty.elim ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      φ.Realize (M := Fin (n ^ k)) (TC.Tuple.closureBy T) Operator.RelEnv.empty Empty.elim := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  have hf {α : Type} (ψ : (language L').Formula α) (v : α × Fin k → Fin n) :
      (I.onFormula ψ).Realize v ↔
        ψ.Realize (M := Fin (n ^ k)) (fun a => lexEquiv (fun i => v (a, i))) :=
    I.realize_onFormula hk ψ (fun a i => v (a, i))
  rw [onTCSentence, Operator.Formula.realize_relabel]
  have h := TC.Tuple.realize_onFormula_closureBy I.onFormula lexEquiv hf hT φ
    Operator.RelEnv.empty Operator.RelEnv.empty (fun {_} r => nomatch r)
    (Empty.elim ∘ Prod.fst)
  convert h using 1
  exact iff_of_eq (congrArg (φ.Realize (TC.Tuple.closureBy T) Operator.RelEnv.empty)
    (Subsingleton.elim _ _))

/-- The sentence pullback preserves truth on the canonical lexicographically ranked universe. -/
theorem realize_onTCSentence (hk : 0 < k)
    (φ : Operator.Formula (language L') TC.shape [] Empty) :
    (I.onTCSentence φ).Realize (M := Fin n) TC.interpretation Operator.RelEnv.empty
        Empty.elim ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      φ.Realize (M := Fin (n ^ k)) TC.interpretation Operator.RelEnv.empty Empty.elim :=
  I.realize_onTCSentence_closureBy TC.Tuple.transports_id hk φ

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
