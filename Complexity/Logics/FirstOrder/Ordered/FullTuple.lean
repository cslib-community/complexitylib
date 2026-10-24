/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.TupleInterpretation
public import Complexity.Logics.FirstOrder.Ordered.TupleBit

/-!
# Canonical ordered interpretations on full tuple universes

Only the formulas for the output input relations are supplied by a client. The full domain,
canonical order, BIT and numeric constants are constructed from the native tuple formulas.
The existing relational interpretation and formula-defined-constant pullback provide the syntax
translation. A language map puts the genuine numeric constants into Mathlib's constant extension;
no numeric relation table or semantic certificate is an input to the construction.
The target input vocabulary is relational; the source vocabulary may contain functions.

For source size at least two and positive tuple dimension, the resulting structure is isomorphic
to its canonically ordered rank universe. Arbitrary restricted domains still require explicit
numeric definitions and their correctness proofs. No ordered machine or capture theorem is asserted.

## Main definitions

* `Cslib.Logic.FO.Ordered.relationalLanguage`, `Cslib.Logic.FO.Ordered.constantsLanguageMap`:
  the relational part of an ordered language and its embedding with numeric constants.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation`: output input-relation formulas.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.toInterpretation`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.constants`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.inputStructure`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.modelStructure`: full relational interpretation,
  constant definitions, and target structures.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.onFormula`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.onSentence`: native constant-aware pullback.

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.modelEquiv`: canonical ordered rank semantics.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.realize_onFormula`: formula truth preservation.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 1.26, Remark 1.32,
  and Exercise 1.33. Formula pullback uses the existing formalization of Proposition 3.5.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- The relation symbols of an ordered language, separated from its numeric constants. -/
abbrev relationalLanguage (L : Language) : Language where
  Functions _ := Empty
  Relations := (language L).Relations

/-- `relationalLanguage L` has no function symbols and is therefore relational. -/
instance (L : Language) : (relationalLanguage L).IsRelational := fun _ => inferInstance

/-- View an ordered relational vocabulary as a relational core with genuine numeric constants. -/
def constantsLanguageMap (L : Language) [L.IsRelational] :
    language L →ᴸ (relationalLanguage L)[[NumericFunction 0]] where
  onFunction {_} f := match f with
    | .inl f => isEmptyElim f
    | .inr .zero => .inr .zero
    | .inr .one => .inr .one
    | .inr .max => .inr .max
  onRelation {_} R := .inl R

/-- A full-tuple ordered interpretation supplies only the definitions of output input relations.
Canonical numeric symbols are supplied by the library's native tuple formulas. -/
structure FullTupleInterpretation (L L' : Language) (k : ℕ) where
  /-- The formula defining an output relation on blocks of `k` source variables. -/
  rel : ∀ {r}, L'.Relations r → (language L).Formula (Fin r × Fin k)

namespace FullTupleInterpretation

variable {L L' : Language} {k : ℕ} (I : FullTupleInterpretation L L' k)

/-- The whole tuple universe, with both input and canonical numeric relation definitions. -/
noncomputable def toInterpretation :
    Interpretation (language L) (relationalLanguage L') (Fin k) where
  domain := ⊤
  rel
    | .inl R => I.rel R
    | .inr .le => tupleLe L k
    | .inr .bit => tupleBit L k

/-- Reuse the coordinate definitions of zero, one and maximum. Dimension zero has no
canonical ordered target and its constant formulas are false. -/
noncomputable def constants : I.toInterpretation.WithConstants (NumericFunction 0) where
  constant := match k with
    | 0 => fun _ => ⊥
    | k + 1 => (tupleConstants L k).constant

variable {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The canonical target constants exist uniquely on every positive-dimensional full domain. -/
theorem constants_valid (hk : 0 < k) : I.constants.Valid (Fin n) := by
  cases k with
  | zero => lia
  | succ k => exact tupleConstants_valid.of_eq rfl rfl

/-- The selected constants have the exact canonical numerical ranks. -/
theorem lexRank_constants_value (hk : 0 < k) (c : NumericFunction 0) :
    lexRank (I.constants.value (I.constants_valid hk (n := n)) c).val = c.index (n ^ k) := by
  cases k with
  | zero => lia
  | succ k =>
    exact (congrArg lexRank
      (Interpretation.WithConstants.val_value_eq rfl rfl tupleConstants_valid
        (I.constants_valid hk (n := n)) c)).trans (lexRank_tupleConstants_value c)

variable [L'.IsRelational]

/-- The target input relations on the canonical rank universe. Numeric symbols are supplied
separately by `numericStructure`, with no target numeric tables as parameters. -/
@[instance_reducible]
def inputStructure : L'.Structure (Fin (n ^ k)) where
  RelMap R x := (I.rel R).Realize fun p => lexEquiv.symm (x p.1) p.2

/-- The actual ordered target structure on interpreted tuples, including numeric constants. -/
@[instance_reducible]
noncomputable def modelStructure (hk : 0 < k) :
    (language L').Structure (I.toInterpretation.Model (Fin n)) :=
  letI := I.constants.modelStructure (I.constants_valid hk (n := n))
  (constantsLanguageMap L').reduct _

/-- The canonical rank universe also has at least two elements. -/
theorem two_le_pow (hk : 0 < k) : 2 ≤ n ^ k :=
  (Fact.out : 2 ≤ n).trans (Nat.le_pow hk)

/-- Ranking the interpreted tuples preserves all input relations and canonical numeric symbols,
including the genuine target constants zero, one and maximum. -/
def modelEquiv (hk : 0 < k) :
    letI := I.modelStructure hk (n := n)
    letI := I.inputStructure (n := n)
    letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
    I.toInterpretation.Model (Fin n) ≃[language L'] Fin (n ^ k) := by
  letI := I.modelStructure hk (n := n)
  letI := I.inputStructure (n := n)
  letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  refine
    { toFun := fun x => lexEquiv x.val
      invFun := fun r => ⟨lexEquiv.symm r, Formula.realize_top.mpr trivial⟩
      left_inv := fun x => Interpretation.Model.ext (lexEquiv.symm_apply_apply x.val)
      right_inv := lexEquiv.apply_symm_apply
      map_fun' := ?_
      map_rel' := ?_ }
  · intro r f x
    cases f with
    | inl f => exact isEmptyElim f
    | inr f =>
      cases f <;> apply Fin.ext
      · exact I.lexRank_constants_value hk .zero
      · exact I.lexRank_constants_value hk .one
      · exact I.lexRank_constants_value hk .max
  · intro r R x
    cases R with
    | inl R =>
      change (I.rel R).Realize (fun p => lexEquiv.symm (lexEquiv (x p.1).val) p.2) ↔
        (I.rel R).Realize (fun p => (x p.1).val p.2)
      simp only [Equiv.symm_apply_apply]
    | inr R =>
      cases R
      · exact (realize_tupleLe (L := L) (fun p => (x p.1).val p.2)).symm
      · exact (realize_tupleBit (L := L) (fun p => (x p.1).val p.2)).symm

variable {α : Type*}

/-- Pull back any ordered target formula, using the existing constant-aware interpretation. -/
noncomputable def onFormula (φ : (language L').Formula α) :
    (language L).Formula (α × Fin k) :=
  I.constants.onFormula ((constantsLanguageMap L').onFormula φ)

/-- Native pullback agrees with evaluation on the canonical rank universe, for every assignment. -/
theorem realize_onFormula (hk : 0 < k) (φ : (language L').Formula α)
    (v : α → Fin k → Fin n) :
    (I.onFormula φ).Realize (fun p => v p.1 p.2) ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      φ.Realize (fun a => lexEquiv (v a)) := by
  let := I.constants.modelStructure (I.constants_valid hk (n := n))
  let := I.modelStructure hk (n := n)
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  let v' : α → I.toInterpretation.Model (Fin n) :=
    fun a => ⟨v a, Formula.realize_top.mpr trivial⟩
  change (I.constants.onFormula ((constantsLanguageMap L').onFormula φ)).Realize
      (fun p => (v' p.1).val p.2) ↔ _
  rw [I.constants.realize_onFormula (I.constants_valid hk), LHom.realize_onFormula]
  exact (StrongHomClass.realize_formula (I.modelEquiv hk) φ).symm

/-- Pull back a sentence over the canonically expanded target language. -/
noncomputable def onSentence (φ : (language L').Sentence) : (language L).Sentence :=
  (I.onFormula φ).relabel Prod.fst

/-- Sentence truth is preserved on the canonical rank universe. -/
theorem realize_onSentence (hk : 0 < k) (φ : (language L').Sentence) :
    Fin n ⊨ I.onSentence φ ↔
      letI := I.inputStructure (n := n)
      letI : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
      Fin (n ^ k) ⊨ φ := by
  let := I.inputStructure (n := n)
  let : Fact (2 ≤ n ^ k) := ⟨two_le_pow (n := n) hk⟩
  rw [onSentence, Sentence.Realize, Formula.realize_relabel, Sentence.Realize]
  convert I.realize_onFormula hk φ (fun a => a.elim) using 1
  · exact iff_of_eq (congrArg (I.onFormula φ).Realize (Subsingleton.elim _ _))
  · exact iff_of_eq (congrArg (Formula.Realize (M := Fin (n ^ k)) φ)
      (Subsingleton.elim _ _))

end FullTupleInterpretation
end Cslib.Logic.FO.Ordered
