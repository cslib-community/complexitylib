/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.FullTuple.Composition

/-! # Non-vacuous canonical full-tuple composition clients -/

@[expose] public section

namespace Cslib.Tests.OrderedComposition

open FirstOrder Language Structure Cslib.Logic.FO Cslib.Logic.FO.Ordered

inductive Relation : ℕ → Type
  | mark : Relation 1

abbrev L : Language where
  Functions _ := Empty
  Relations := Relation

instance : L.IsRelational := fun _ => inferInstance

instance {n : ℕ} : L.Structure (Fin n) where
  RelMap r x := match r with | .mark => (x 0).val = 1

instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩

/-- The first coordinate must be marked and the second must have bit one set. -/
def inner : FullTupleInterpretation L L 2 where
  rel r := match r with
    | .mark => (LHom.sumInl : L →ᴸ language L).onFormula
        (Relations.formula₁ Relation.mark (.var (0, 0))) ⊓
      bit L (.var (0, 1)) (one L)

/-- A target input relation and a numeric test occur in the same relation definition. -/
def outer : FullTupleInterpretation L L 3 where
  rel r := match r with
    | .mark => (LHom.sumInl : L →ᴸ language L).onFormula
        (Relations.formula₁ Relation.mark (.var (0, 1))) ⊓
      bit L (.var (0, 2)) (one L)

def rows : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![1, 2], ![2, 0] ]

/-- Flattened tuple ranks and constant validity across `inner`, `outer.comp inner`, and dimension
`0`. -/
example (I : FullTupleInterpretation L L 0) :
    (fun j => lexRank (rows j)) = ![1, 5, 6] ∧
    lexRank (flattenTuple rows) = 132 ∧
    lexRank (flattenTuple (fun i j => rows j i)) = 150 ∧
    lexRank (flattenTuple rows) = lexRank (fun j => lexEquiv (rows j)) ∧
    inner.constants.Valid (Fin 2) ∧
    ¬I.constants.Valid (Fin 3) ∧
    (outer.comp inner).constants.Valid (Fin 3) ∧
    lexRank ((outer.comp inner).constants.value
      ((outer.comp inner).constants_valid (n := 3) (by decide)) .one).val = 1 :=
  ⟨by decide, by decide, by decide, lexRank_flattenTuple rows,
    inner.constants_valid (by decide),
    fun h => let ⟨_, hx, _⟩ := h .zero; hx,
    (outer.comp inner).constants_valid (by decide),
    (outer.comp inner).lexRank_constants_value (by decide) .one⟩

/-- Both input relation tests in this composite are true, with nontrivial numeric conjuncts. -/
example : ((outer.comp inner).rel Relation.mark).Realize
    (fun p => flattenTuple rows p.2) := by
  rw [outer.realize_comp_rel inner (by decide) Relation.mark (fun _ => rows)]
  simp only [outer, Formula.realize_inf, realize_inputFormula, Formula.realize_rel₁,
    realize_bit, Term.realize_var, realize_one_val]
  change ((inner.rel Relation.mark).Realize (fun p => lexEquiv.symm (lexEquiv (rows 1)) p.2)) ∧
    (lexRank (rows 2)).testBit 1 = true
  simp only [Equiv.symm_apply_apply, inner, Formula.realize_inf, realize_inputFormula,
    Formula.realize_rel₁, Term.realize_var, realize_bit, realize_one_val]
  change ((rows 1 0).val = 1 ∧ (rows 1 1).val.testBit 1 = true) ∧
    (lexRank (rows 2)).testBit 1 = true
  decide

def bitQuery : (language L).Formula (Fin 2) := bit L (.var 0) (.var 1)

/-- Index seven is larger than the base universe (value rank `132`), while a maximal index is
rejected by the composite native BIT pullback. -/
example :
    ((outer.comp inner).onFormula bitQuery).Realize
      (fun p => if p.1 = 0 then flattenTuple rows p.2 else
        (![0, 0, 0, 0, 2, 1] : Fin 6 → Fin 3) p.2) ∧
    ¬((outer.comp inner).onFormula bitQuery).Realize
      (fun p => if p.1 = 0 then flattenTuple rows p.2 else (2 : Fin 3)) := by
  let := (outer.comp inner).inputStructure (n := 3)
  let : Fact (2 ≤ 3 ^ (3 * 2)) := ⟨by decide⟩
  refine ⟨?_, ?_⟩
  · rw [(outer.comp inner).realize_onFormula (by decide) bitQuery
      (fun a i => if a = 0 then flattenTuple rows i else ![0, 0, 0, 0, 2, 1] i)]
    rw [bitQuery, realize_bit]
    decide
  · rw [(outer.comp inner).realize_onFormula (by decide) bitQuery
      (fun a i => if a = 0 then flattenTuple rows i else 2)]
    rw [bitQuery, realize_bit]
    decide

/-- Genuine numeric constants occur under a universal quantifier. -/
noncomputable def oneBits : (language L).Sentence :=
  closeAll Unit ((bit L (one L) (.var ())).iff ((Term.var ()).equal (zero L)))

-- Composition commutes with `onSentence` and `onFormula` for the concrete queries below.
example (v : Fin 2 → Fin 3 → Fin 2 → Fin 3) :
    Fin 3 ⊨ (outer.comp inner).onSentence oneBits ∧
    (Fin 3 ⊨ (outer.comp inner).onSentence oneBits ↔
      Fin 3 ⊨ inner.onSentence (outer.onSentence oneBits)) ∧
    (((outer.comp inner).onFormula bitQuery).Realize (fun p => flattenTuple (v p.1) p.2) ↔
      (inner.onFormula (outer.onFormula bitQuery)).Realize (fun p => v p.1.1 p.1.2 p.2)) := by
  refine ⟨?_,
    outer.realize_comp_onSentence inner (by decide) (by decide) oneBits,
    outer.realize_comp_onFormula inner (by decide) (by decide) bitQuery v⟩
  rw [(outer.comp inner).realize_onSentence (by decide)]
  simp only [oneBits, realize_closeAll, Formula.realize_iff, realize_bit,
    Formula.realize_equal, Term.realize_var, realize_one_val]
  intro u
  change ((1 : ℕ).testBit (u ()).val = true) ↔ u () = 0
  rw [Nat.testBit_one_eq_true_iff_self_eq_zero, Fin.ext_iff]
  rfl

end Cslib.Tests.OrderedComposition
