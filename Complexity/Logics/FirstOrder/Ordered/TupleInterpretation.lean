/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Tuple
public import Complexity.Logics.FirstOrder.Ordered.Constants
public import Complexity.Logics.FirstOrder.QuantifierFree
import Complexity.Tactic.FirstOrder

/-!
# Order and constants on full tuple universes

Finite disjunctions and conjunctions express first-difference lexicographic order without
quantifiers. On every canonical base structure `Fin n`, `n ≥ 2`, the formulas agree with the
arbitrary-base ranks in `Ordered.lexEquiv`. For positive tuple dimension, coordinate equalities
define canonical zero, one and maximum as target constants through the existing constant-aware
interpretation API. Their ranks are exactly `0`, `1` and `n ^ k - 1`.

The interpreted universe here consists of all tuples. Successor and BIT lifting are supplied
separately in `Ordered.TupleSuccessor` and `Ordered.TupleBit`; canonical interpretations and their
composition are in `Ordered.FullTuple` and `Ordered.FullTuple.Composition`. These results do not
infer numeric predicates for arbitrary restricted domains.

## Main definitions

* `Cslib.Logic.FO.Ordered.tupleLt`, `Cslib.Logic.FO.Ordered.tupleLe`: native tuple-order formulas.
* `Cslib.Logic.FO.Ordered.fullTuple`: the full tuple domain, with empty relational target language.
* `Cslib.Logic.FO.Ordered.constantTuple`, `Cslib.Logic.FO.Ordered.tupleConstants`: the canonical
  constant tuples and the coordinate definitions of the canonical target constants.

## Main results

* `Cslib.Logic.FO.Ordered.realize_tupleLt`, `Cslib.Logic.FO.Ordered.realize_tupleLe`:
  rank semantics.
* `Cslib.Logic.FO.Ordered.isQF_tupleLt`, `Cslib.Logic.FO.Ordered.isQF_tupleLe`:
  quantifier-freeness.
* `Cslib.Logic.FO.Ordered.tupleConstants_valid`: unique selection in the full tuple domain.
* `Cslib.Logic.FO.Ordered.lexRank_tupleConstants_value`: exact interpreted constant ranks.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33(1).
  `Ordered.TupleBit` supplies the full-domain BIT lifting in Exercise 1.33(3).
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- The canonical order relation formula `le L s t` is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_le (L : Language) {α : Type*} (s t : (language L).Term α) :
    (le L s t).IsAtomic :=
  .rel _ _

/-- The canonical `BIT` relation formula `bit L s i` is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_bit (L : Language) {α : Type*} (s i : (language L).Term α) :
    (bit L s i).IsAtomic :=
  .rel _ _

/-- Strict tuple order: one coordinate increases and all earlier coordinates agree. -/
noncomputable def tupleLt (L : Language) (k : ℕ) : (language L).Formula (Fin 2 × Fin k) :=
  Formula.iSup fun i : Fin k =>
    (le L (.var (1, i)) (.var (0, i))).not ⊓
      Formula.iInf fun j : Fin k =>
        if j < i then Term.equal (.var (0, j)) (.var (1, j)) else ⊤

/-- Weak tuple order, expressed without quantifiers by reversing strict order. -/
noncomputable def tupleLe (L : Language) (k : ℕ) : (language L).Formula (Fin 2 × Fin k) :=
  ((tupleLt L k).relabel fun p => (p.1.rev, p.2)).not

/-- The lexicographic order formula on tuples is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_tupleLt (L : Language) (k : ℕ) : (tupleLt L k).IsQF := by
  unfold tupleLt; fo_qf

/-- The lexicographic weak order formula on tuples is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_tupleLe (L : Language) (k : ℕ) : (tupleLe L k).IsQF := by
  unfold tupleLe; fo_qf

variable {L : Language} {n k : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The strict-order formula compares the canonical lexicographic ranks. -/
@[simp, fo_realize]
theorem realize_tupleLt (v : Fin 2 × Fin k → Fin n) :
    (tupleLt L k).Realize v ↔ lexRank (fun i => v (0, i)) < lexRank (fun i => v (1, i)) := by
  fo_simp [tupleLt, not_le, lexRank_lt_iff]
  refine exists_congr fun i => and_congr_right fun _ => forall_congr' fun j => ?_
  by_cases hji : j < i <;> simp [hji]

/-- The weak-order formula compares the canonical lexicographic ranks. -/
@[simp, fo_realize]
theorem realize_tupleLe (v : Fin 2 × Fin k → Fin n) :
    (tupleLe L k).Realize v ↔ lexRank (fun i => v (0, i)) ≤ lexRank (fun i => v (1, i)) := by
  fo_simp [tupleLe]
  exact not_lt

/-- The whole tuple universe, with no additional target relation symbols. -/
def fullTuple (L : Language) (k : ℕ) : Interpretation (language L) Language.empty (Fin k) where
  domain := ⊤
  rel r := r.elim

/-- The canonical full-domain tuple corresponding to a numeric constant symbol. -/
def constantTuple (c : NumericFunction 0) : Fin (k + 1) → Fin n :=
  match c with | .zero => tupleZero | .one => tupleOne | .max => tupleMax

/-- Define each target constant by coordinate equalities to canonical source constants. -/
noncomputable def tupleConstants (L : Language) (k : ℕ) :
    (fullTuple L (k + 1)).WithConstants (NumericFunction 0) where
  constant c := Formula.iInf fun i : Fin (k + 1) => Term.equal (.var i)
    (match c with
    | .zero => zero L
    | .one => if i = Fin.last k then one L else zero L
    | .max => max L)

/-- The constant definitions select exactly their explicit canonical coordinate tuples. -/
theorem realize_tupleConstants (c : NumericFunction 0) (x : Fin (k + 1) → Fin n) :
    ((tupleConstants L k).constant c).Realize x ↔ x = constantTuple c := by
  simp only [tupleConstants, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
    funext_iff]
  apply forall_congr'
  intro i
  cases c with
  | zero => rfl
  | one =>
    by_cases hi : i = Fin.last k <;>
      simp only [hi, constantTuple, tupleOne, tupleZero, ite_true, ite_false] <;> rfl
  | max => rfl

/-- The full-domain constant definitions are quantifier-free. -/
theorem isQF_tupleConstants (L : Language) (k : ℕ) (c : NumericFunction 0) :
    ((tupleConstants L k).constant c).IsQF :=
  Formula.isQF_iInf _ fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF

/-- Canonical tuple constants exist uniquely for every base `n ≥ 2` and positive dimension. -/
theorem tupleConstants_valid : (tupleConstants L k).Valid (Fin n) := by
  intro c
  refine ⟨⟨constantTuple c, Formula.realize_top.mpr trivial⟩,
    (realize_tupleConstants c _).mpr rfl, ?_⟩
  intro x hx
  exact Interpretation.Model.ext ((realize_tupleConstants c x.val).mp hx)

/-- The canonical constant tuples have ranks `0`, `1` and `n ^ (k + 1) - 1`. -/
theorem lexRank_constantTuple (c : NumericFunction 0) :
    lexRank (constantTuple (n := n) (k := k) c) = c.index (n ^ (k + 1)) := by
  cases c
  · exact lexRank_tupleZero
  · exact lexRank_tupleOne
  · exact lexRank_tupleMax

/-- The interpreted constant values have exactly the canonical numerical ranks. -/
theorem lexRank_tupleConstants_value (c : NumericFunction 0) :
    lexRank ((tupleConstants L k).value (tupleConstants_valid (n := n)) c).val =
      c.index (n ^ (k + 1)) := by
  rw [(realize_tupleConstants c _).mp
    ((tupleConstants L k).value_spec (tupleConstants_valid (n := n)) c)]
  exact lexRank_constantTuple c

end Cslib.Logic.FO.Ordered
