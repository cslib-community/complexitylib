/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.TupleInterpretation

/-! # Arbitrary-base tuple numbering, order formulas and interpreted constants -/

@[expose] public section

namespace Cslib.Tests.OrderedTuples

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩

/-- These tuples reverse their relative order under the old colexicographic numbering. -/
def x : Fin 2 → Fin 3 := ![0, 2]
def y : Fin 2 → Fin 3 := ![1, 0]

/-- Lexicographic vs. colexicographic tuple numbering, base-five digits, zero-dimensional universe,
and endpoint tuples (`tupleZero`, `tupleOne`, `tupleMax`). -/
example :
    lexRank x = 2 ∧
    lexRank y = 3 ∧
    tupleIndex x = 6 ∧
    tupleIndex y = 1 ∧
    lexRank x < lexRank y ∧
    tupleIndex y < tupleIndex x ∧
    Pi.Lex (· < ·) (· < ·) x y ∧
    lexRank (![3, 2] : Fin 2 → Fin 5) = 17 ∧
    ((lexEquiv.symm (17 : Fin (5 ^ 2))) 0).val = 3 ∧
    ((lexEquiv.symm (17 : Fin (5 ^ 2))) 1).val = 2 ∧
    lexRank (Fin.elim0 : Fin 0 → Fin 0) = 0 ∧
    lexRank (tupleZero (n := 3) (k := 2)) = 0 ∧
    lexRank (tupleOne (n := 3) (k := 1)) = 1 ∧
    lexRank (tupleMax (n := 3) (k := 2)) = 8 ∧
    lexRank (tupleMax (n := 5) (k := 3)) = 124 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (lexRank_lt_iff_lex x y).mp (by decide),
    by decide,
    by rw [lexEquiv_symm_apply_val]; decide,
    by rw [lexEquiv_symm_apply_val]; decide,
    by rw [lexRank_apply]; simp,
    lexRank_tupleZero, lexRank_tupleOne, lexRank_tupleMax, lexRank_tupleMax⟩

/-- Quantifier-freeness and realization of `tupleLt`, `tupleLe`, and `tupleConstants`. -/
example :
    (tupleLt L 2).IsQF ∧
    (tupleLe L 2).IsQF ∧
    (tupleLt L 2).Realize (fun p => if p.1 = 0 then x p.2 else y p.2) ∧
    ¬ (tupleLe L 2).Realize (fun p => if p.1 = 0 then y p.2 else x p.2) ∧
    (tupleLe L 0).Realize (fun p => p.2.elim0 : Fin 2 × Fin 0 → Fin 3) ∧
    (tupleConstants L 1).Valid (Fin 3) ∧
    ((tupleConstants L 1).constant .one).IsQF ∧
    ((tupleConstants L 1).constant .one).Realize (![0, 1] : Fin 2 → Fin 3) ∧
    lexRank ((tupleConstants L 1).value (tupleConstants_valid (n := 3)) .max).val = 8 ∧
    lexRank ((tupleConstants L 2).value (tupleConstants_valid (n := 5)) .one).val = 1 :=
  ⟨isQF_tupleLt L 2, isQF_tupleLe L 2,
    by rw [realize_tupleLt]; decide,
    by rw [realize_tupleLe]; decide,
    by rw [realize_tupleLe],
    tupleConstants_valid, isQF_tupleConstants L 1 .one,
    by rw [realize_tupleConstants]; decide,
    lexRank_tupleConstants_value .max,
    lexRank_tupleConstants_value .one⟩

/-- A sentence with target constants pulls back through the full tuple interpretation. -/
def separated : Language.empty[[NumericFunction 0]].Sentence :=
  ((Language.empty.con .zero).term.equal (Language.empty.con .one).term).not

example : Fin 3 ⊨ (tupleConstants L 1).onSentence separated := by
  rw [(tupleConstants L 1).realize_onSentence tupleConstants_valid]
  simp only [separated, Sentence.Realize, Formula.realize_not, Formula.realize_equal,
    Term.realize_constants]
  intro h
  have hr := congrArg (fun z : (fullTuple L 2).Model (Fin 3) => lexRank z.val) h
  change lexRank ((tupleConstants L 1).value tupleConstants_valid .zero).val =
    lexRank ((tupleConstants L 1).value tupleConstants_valid .one).val at hr
  simp only [lexRank_tupleConstants_value] at hr
  contradiction

end Cslib.Tests.OrderedTuples
