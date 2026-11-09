/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.TupleSuccessor

/-! # Non-wrapping arbitrary-base successor and native carry compilation -/

@[expose] public section

namespace Cslib.Tests.OrderedSuccessor

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 3) := ⟨by decide⟩
instance : Fact (2 ≤ 5) := ⟨by decide⟩

def tuplePair {n k : ℕ} (x y : Fin k → Fin n) : Fin 2 × Fin k → Fin n :=
  fun p => ![x, y] p.1 p.2

/-- An ordinary digit increment in base three. -/
example : (tupleSucc L 2).Realize (tuplePair (![1, 0] : Fin 2 → Fin 3) ![1, 1]) := by
  rw [realize_tupleSucc]
  decide

/-- A carry changes the most significant coordinate, not the least significant convention. -/
example : (tupleSucc L 2).Realize (tuplePair (![0, 2] : Fin 2 → Fin 3) ![1, 0]) := by
  rw [realize_tupleSucc]
  decide

/-- The carry condition itself is inhabited, including multiple trailing maximum digits. -/
example : IsCarrySuccessor (![0, 2, 2] : Fin 3 → Fin 3) ![1, 0, 0] := by
  rw [isCarrySuccessor_iff]
  decide

example : (tupleSucc L 3).Realize (tuplePair (![2, 4, 4] : Fin 3 → Fin 5) ![3, 0, 0]) := by
  rw [realize_tupleSucc]
  decide

/-- Increasing rank by more than one is rejected. -/
example : ¬(tupleSucc L 2).Realize (tuplePair (![0, 2] : Fin 2 → Fin 3) ![1, 1]) := by
  rw [realize_tupleSucc]
  decide

/-- There is no wrap from maximum to zero. -/
example : ¬(tupleSucc L 2).Realize (tuplePair (tupleMax (n := 3)) tupleZero) := by
  apply not_realize_tupleSucc_of_max
  rfl

example (v : Fin 2 × Fin 0 → Fin 3) : ¬(tupleSucc L 0).Realize v :=
  not_realize_tupleSucc_zero v

example : (successor L).Realize (![1, 2] : Fin 2 → Fin 3) := by
  rw [realize_successor]
  decide

example : ¬(successor L).Realize (![2, 0] : Fin 2 → Fin 3) := by
  rw [realize_successor]
  decide

/-- A genuine source vocabulary with an atomic successor predicate. -/
inductive SuccRelation : ℕ → Type
  | succ : SuccRelation 2

abbrev S : Language := ⟨fun _ => Empty, SuccRelation⟩

instance {n : ℕ} : S.Structure (Fin n) where
  funMap f := f.elim
  RelMap | .succ, v => (v 1).val = (v 0).val + 1

def atomicSuccessor : (language S).Formula (Fin 2) :=
  (LHom.sumInl : S →ᴸ language S).onFormula
    (Relations.formula (L := S) SuccRelation.succ fun i => .var i)

/-- The supplied quantifier-free successor has a genuine canonical model. -/
theorem atomicSuccessor_correct (v : Fin 2 → Fin 3) :
    atomicSuccessor.Realize v ↔ (v 1).val = (v 0).val + 1 := by
  rw [atomicSuccessor, LHom.realize_onFormula, Formula.realize_rel]
  rfl

example : (tupleSuccOf atomicSuccessor 2).IsQF := by
  apply isQF_tupleSuccOf
  exact (BoundedFormula.IsAtomic.rel _ _).isQF.onFormula _

/-- The generic compiler is exercised on its atomic, quantifier-free source instance. -/
example : (tupleSuccOf atomicSuccessor 2).Realize
    (tuplePair (![0, 2] : Fin 2 → Fin 3) ![1, 0]) := by
  rw [realize_tupleSuccOf atomicSuccessor_correct]
  decide

end Cslib.Tests.OrderedSuccessor
